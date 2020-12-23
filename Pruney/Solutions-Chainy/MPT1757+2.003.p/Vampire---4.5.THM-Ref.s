%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 704 expanded)
%              Number of leaves         :   12 ( 125 expanded)
%              Depth                    :   36
%              Number of atoms          :  724 (7821 expanded)
%              Number of equality atoms :   19 ( 418 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(global_subsumption,[],[f81,f164,f181])).

fof(f181,plain,(
    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f180,f80])).

fof(f80,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
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
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
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

fof(f38,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f180,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f179,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f179,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(resolution,[],[f178,f43])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f177,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f177,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f176,f40])).

fof(f40,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f175,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f174,f45])).

fof(f45,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f174,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f173,f44])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f173,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f172,f49])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f172,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f171,f48])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f170,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f169,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f167,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) ) ),
    inference(resolution,[],[f164,f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f164,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(resolution,[],[f162,f135])).

fof(f135,plain,
    ( ~ sP7(sK3,sK1,sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f134,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f133,f80])).

fof(f133,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f132,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f131,f43])).

fof(f131,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f130,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f129,f46])).

fof(f129,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f127,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f126,f49])).

fof(f126,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f125,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f124,f47])).

fof(f124,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f123,f52])).

fof(f123,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ sP7(sK3,sK1,sK4) ),
    inference(resolution,[],[f82,f79])).

% (24885)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f79,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
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
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ sP7(X3,X1,X6) ) ),
    inference(general_splitting,[],[f70,f78_D])).

fof(f78,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | sP7(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f78_D])).

fof(f78_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ v3_pre_topc(X4,X1)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r2_hidden(X6,X4)
          | ~ r1_tarski(X4,u1_struct_0(X3)) )
    <=> ~ sP7(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

% (24879)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f70,plain,(
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
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f82,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f36,f39])).

fof(f36,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f162,plain,(
    sP7(sK3,sK1,sK4) ),
    inference(resolution,[],[f155,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f155,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
      | sP7(X0,sK1,sK4) ) ),
    inference(resolution,[],[f154,f149])).

fof(f149,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
      | sP7(X3,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f147,f92])).

fof(f92,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
      | sP7(X3,sK1,X2) ) ),
    inference(resolution,[],[f144,f78])).

fof(f144,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(resolution,[],[f86,f92])).

fof(f86,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(subsumption_resolution,[],[f85,f43])).

% (24877)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f85,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f84,f48])).

fof(f84,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f42,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f42,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,(
    r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f116,f110])).

fof(f110,plain,(
    m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f109,f41])).

fof(f109,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f91,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f87,f49])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f108,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f106,f97])).

fof(f97,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f96,f48])).

fof(f96,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f106,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(X0))
      | r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f113,plain,(
    r2_hidden(sK4,k1_connsp_2(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f112,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(sK4,k1_connsp_2(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f111,f91])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | r2_hidden(sK4,k1_connsp_2(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f107,f97])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | r2_hidden(sK4,k1_connsp_2(sK3,sK4)) ),
    inference(resolution,[],[f80,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_connsp_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f81,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f37,f39])).

fof(f37,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (24881)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (24884)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (24878)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (24895)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (24876)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (24881)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(global_subsumption,[],[f81,f164,f181])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f38,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    sK4 = sK5),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f179,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.22/0.51    inference(resolution,[],[f178,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK4,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f177,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f175,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v2_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) )),
% 0.22/0.51    inference(resolution,[],[f164,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X1,X0,X2,X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(equality_resolution,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(resolution,[],[f162,f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ~sP7(sK3,sK1,sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f50])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f80])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f40])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f43])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f130,f41])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f46])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f45])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f44])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f126,f49])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f48])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f47])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f123,f52])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f51])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(resolution,[],[f82,f79])).
% 0.22/0.51  % (24885)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X6) | ~sP7(X3,X1,X6)) )),
% 0.22/0.51    inference(general_splitting,[],[f70,f78_D])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X6,X4,X3,X1] : (~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | sP7(X3,X1,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f78_D])).
% 0.22/0.51  fof(f78_D,plain,(
% 0.22/0.51    ( ! [X6,X1,X3] : (( ! [X4] : (~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3))) ) <=> ~sP7(X3,X1,X6)) )),
% 0.22/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.51  % (24879)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.22/0.51    inference(equality_resolution,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(forward_demodulation,[],[f36,f39])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    sP7(sK3,sK1,sK4)),
% 0.22/0.51    inference(resolution,[],[f155,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) | sP7(X0,sK1,sK4)) )),
% 0.22/0.51    inference(resolution,[],[f154,f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | sP7(X3,sK1,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f88,f49])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    inference(resolution,[],[f43,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X2,u1_struct_0(sK3)) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | sP7(X3,sK1,X2)) )),
% 0.22/0.51    inference(resolution,[],[f144,f78])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.22/0.51    inference(resolution,[],[f86,f92])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f85,f43])).
% 0.22/0.51  % (24877)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f48])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f83,f49])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.22/0.51    inference(resolution,[],[f42,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v1_tsep_1(sK3,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    r2_hidden(sK4,u1_struct_0(sK3))),
% 0.22/0.51    inference(resolution,[],[f116,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f41])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    v2_struct_0(sK3) | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f87,f49])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f43,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f48])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f90,f49])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f43,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(resolution,[],[f80,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(X0)) | r2_hidden(sK4,X0)) )),
% 0.22/0.51    inference(resolution,[],[f113,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    r2_hidden(sK4,k1_connsp_2(sK3,sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f41])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    v2_struct_0(sK3) | r2_hidden(sK4,k1_connsp_2(sK3,sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f111,f91])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | r2_hidden(sK4,k1_connsp_2(sK3,sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f97])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | r2_hidden(sK4,k1_connsp_2(sK3,sK4))),
% 0.22/0.51    inference(resolution,[],[f80,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(X1,k1_connsp_2(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(forward_demodulation,[],[f37,f39])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (24881)------------------------------
% 0.22/0.51  % (24881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24881)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (24881)Memory used [KB]: 6268
% 0.22/0.51  % (24881)Time elapsed: 0.100 s
% 0.22/0.51  % (24881)------------------------------
% 0.22/0.51  % (24881)------------------------------
% 0.22/0.51  % (24882)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (24875)Success in time 0.147 s
%------------------------------------------------------------------------------
