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
% DateTime   : Thu Dec  3 13:18:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 981 expanded)
%              Number of leaves         :   13 ( 172 expanded)
%              Depth                    :   35
%              Number of atoms          :  879 (10642 expanded)
%              Number of equality atoms :   17 ( 558 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(subsumption_resolution,[],[f583,f173])).

fof(f173,plain,(
    ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f84,f172])).

fof(f172,plain,(
    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f171,f85])).

fof(f85,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f41,f44])).

fof(f44,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f41,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f170,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f170,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f169,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f169,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f166,f48])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f166,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(resolution,[],[f124,f83])).

fof(f83,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f121,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f84,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f42,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f583,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f582,f56])).

fof(f582,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f581,f269])).

fof(f269,plain,(
    m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) ),
    inference(subsumption_resolution,[],[f264,f45])).

fof(f264,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) ),
    inference(resolution,[],[f222,f139])).

fof(f139,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) ) ),
    inference(subsumption_resolution,[],[f138,f103])).

fof(f103,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f102,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f101,f53])).

fof(f101,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f87,f47])).

fof(f47,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f138,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK3))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK3))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f136,f54])).

fof(f136,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK3))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f127,f53])).

fof(f127,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK3))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f98,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f59,f48])).

fof(f222,plain,(
    r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f203,f163])).

fof(f163,plain,(
    r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f162,f46])).

fof(f162,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f161,f83])).

fof(f161,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f160,f92])).

fof(f92,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f91,f54])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f160,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f155,f95])).

fof(f95,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f94,f53])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f93,f54])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f155,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(resolution,[],[f111,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f111,plain,(
    m1_connsp_2(sK8(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f110,plain,
    ( v2_struct_0(sK3)
    | m1_connsp_2(sK8(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f109,f92])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK8(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f105,f95])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK8(sK3,sK4),sK3,sK4) ),
    inference(resolution,[],[f76,f83])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
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
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f203,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK8(sK3,sK4))
      | r2_hidden(X3,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f159,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f159,plain,(
    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f158,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f157,f83])).

fof(f157,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f156,f92])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f154,f95])).

fof(f154,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f111,f75])).

fof(f581,plain,
    ( ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f580,f55])).

fof(f580,plain,
    ( v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f579,f83])).

fof(f579,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f578,f48])).

fof(f578,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f577,f51])).

fof(f577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f576,f50])).

fof(f576,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f575,f49])).

fof(f575,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f574,f54])).

fof(f574,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f573,f53])).

fof(f573,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f572,f52])).

fof(f572,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f571,f57])).

fof(f571,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(resolution,[],[f324,f172])).

fof(f324,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | v2_struct_0(X0)
      | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),X1,X3)
      | ~ v2_pre_topc(X0)
      | r1_tmap_1(X1,X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f323,f46])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | v2_struct_0(X0)
      | ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),X1,X3)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X3)
      | r1_tmap_1(X1,X0,X2,X3) ) ),
    inference(resolution,[],[f268,f90])).

fof(f90,plain,(
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
    inference(subsumption_resolution,[],[f89,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f89,plain,(
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
    inference(subsumption_resolution,[],[f80,f75])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f268,plain,(
    r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f263,f45])).

fof(f263,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f222,f143])).

fof(f143,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f142,f103])).

fof(f142,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,(
    ! [X2] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f140,f54])).

fof(f140,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1) ) ),
    inference(resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_tarski(sK7(X0,X1,X2),X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (946)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.43  % (946)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f584,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f583,f173])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f84,f172])).
% 0.20/0.43  fof(f172,plain,(
% 0.20/0.43    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f171,f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(forward_demodulation,[],[f41,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    sK4 = sK5),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f14])).
% 0.20/0.43  fof(f14,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f170,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ~v2_struct_0(sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f170,plain,(
% 0.20/0.43    v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f169,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    ~m1_subset_1(sK4,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f166,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    m1_pre_topc(sK3,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.43    inference(resolution,[],[f124,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.43    inference(forward_demodulation,[],[f43,f44])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(X0) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f123,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f122,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f121,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    v1_funct_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f120,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    l1_pre_topc(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f119,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    v2_pre_topc(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f118,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ~v2_struct_0(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f117,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f116,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    v2_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.20/0.43    inference(resolution,[],[f78,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.43    inference(equality_resolution,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(forward_demodulation,[],[f42,f44])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f583,plain,(
% 0.20/0.43    r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f582,f56])).
% 0.20/0.43  fof(f582,plain,(
% 0.20/0.43    ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f581,f269])).
% 0.20/0.43  fof(f269,plain,(
% 0.20/0.43    m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f264,f45])).
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    ~m1_subset_1(sK4,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)),
% 0.20/0.43    inference(resolution,[],[f222,f139])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f138,f103])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f102,f48])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f101,f53])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f100,f54])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.20/0.43    inference(resolution,[],[f87,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    v1_tsep_1(sK3,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f82,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f137,f52])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    ( ! [X1] : (v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f136,f54])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ( ! [X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f127,f53])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ( ! [X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.43    inference(resolution,[],[f98,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f97,f54])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.43    inference(resolution,[],[f59,f48])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    r2_hidden(sK4,u1_struct_0(sK3))),
% 0.20/0.43    inference(resolution,[],[f203,f163])).
% 0.20/0.44  fof(f163,plain,(
% 0.20/0.44    r2_hidden(sK4,sK8(sK3,sK4))),
% 0.20/0.44    inference(subsumption_resolution,[],[f162,f46])).
% 0.20/0.44  fof(f162,plain,(
% 0.20/0.44    v2_struct_0(sK3) | r2_hidden(sK4,sK8(sK3,sK4))),
% 0.20/0.44    inference(subsumption_resolution,[],[f161,f83])).
% 0.20/0.44  fof(f161,plain,(
% 0.20/0.44    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK8(sK3,sK4))),
% 0.20/0.44    inference(subsumption_resolution,[],[f160,f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    l1_pre_topc(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f91,f54])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.20/0.44    inference(resolution,[],[f58,f48])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.44  fof(f160,plain,(
% 0.20/0.44    ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK8(sK3,sK4))),
% 0.20/0.44    inference(subsumption_resolution,[],[f155,f95])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    v2_pre_topc(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f94,f53])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f93,f54])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.20/0.44    inference(resolution,[],[f71,f48])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.44  fof(f155,plain,(
% 0.20/0.44    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK8(sK3,sK4))),
% 0.20/0.44    inference(resolution,[],[f111,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,X1)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f66,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    m1_connsp_2(sK8(sK3,sK4),sK3,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f110,f46])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    v2_struct_0(sK3) | m1_connsp_2(sK8(sK3,sK4),sK3,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f109,f92])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK8(sK3,sK4),sK3,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f105,f95])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK8(sK3,sK4),sK3,sK4)),
% 0.20/0.44    inference(resolution,[],[f76,f83])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK8(X0,X1),X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.20/0.44  fof(f203,plain,(
% 0.20/0.44    ( ! [X3] : (~r2_hidden(X3,sK8(sK3,sK4)) | r2_hidden(X3,u1_struct_0(sK3))) )),
% 0.20/0.44    inference(resolution,[],[f159,f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.44  fof(f159,plain,(
% 0.20/0.44    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f158,f46])).
% 0.20/0.44  fof(f158,plain,(
% 0.20/0.44    v2_struct_0(sK3) | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f157,f83])).
% 0.20/0.44  fof(f157,plain,(
% 0.20/0.44    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f156,f92])).
% 0.20/0.44  fof(f156,plain,(
% 0.20/0.44    ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f154,f95])).
% 0.20/0.44  fof(f154,plain,(
% 0.20/0.44    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.44    inference(resolution,[],[f111,f75])).
% 0.20/0.44  fof(f581,plain,(
% 0.20/0.44    ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f580,f55])).
% 0.20/0.44  fof(f580,plain,(
% 0.20/0.44    v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f579,f83])).
% 0.20/0.44  fof(f579,plain,(
% 0.20/0.44    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f578,f48])).
% 0.20/0.44  fof(f578,plain,(
% 0.20/0.44    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f577,f51])).
% 0.20/0.44  fof(f577,plain,(
% 0.20/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f576,f50])).
% 0.20/0.44  fof(f576,plain,(
% 0.20/0.44    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f575,f49])).
% 0.20/0.44  fof(f575,plain,(
% 0.20/0.44    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f574,f54])).
% 0.20/0.44  fof(f574,plain,(
% 0.20/0.44    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f573,f53])).
% 0.20/0.44  fof(f573,plain,(
% 0.20/0.44    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f572,f52])).
% 0.20/0.44  fof(f572,plain,(
% 0.20/0.44    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f571,f57])).
% 0.20/0.44  fof(f571,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.44    inference(resolution,[],[f324,f172])).
% 0.20/0.44  fof(f324,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | v2_struct_0(X0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),X1,X3) | ~v2_pre_topc(X0) | r1_tmap_1(X1,X0,X2,X3)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f323,f46])).
% 0.20/0.44  fof(f323,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X3,u1_struct_0(sK3)) | v2_struct_0(X0) | ~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),X1,X3) | ~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X3) | r1_tmap_1(X1,X0,X2,X3)) )),
% 0.20/0.44    inference(resolution,[],[f268,f90])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tarski(X4,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | v2_struct_0(X0) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f89,f70])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f80,f75])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.44    inference(equality_resolution,[],[f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.44  fof(f268,plain,(
% 0.20/0.44    r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3))),
% 0.20/0.44    inference(subsumption_resolution,[],[f263,f45])).
% 0.20/0.44  fof(f263,plain,(
% 0.20/0.44    ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3))),
% 0.20/0.44    inference(resolution,[],[f222,f143])).
% 0.20/0.44  fof(f143,plain,(
% 0.20/0.44    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f142,f103])).
% 0.20/0.44  fof(f142,plain,(
% 0.20/0.44    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f141,f52])).
% 0.20/0.44  fof(f141,plain,(
% 0.20/0.44    ( ! [X2] : (v2_struct_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f140,f54])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    ( ! [X2] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f128,f53])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    ( ! [X2] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) )),
% 0.20/0.44    inference(resolution,[],[f98,f63])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK7(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (946)------------------------------
% 0.20/0.44  % (946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (946)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (946)Memory used [KB]: 2046
% 0.20/0.44  % (946)Time elapsed: 0.017 s
% 0.20/0.44  % (946)------------------------------
% 0.20/0.44  % (946)------------------------------
% 0.20/0.44  % (928)Success in time 0.086 s
%------------------------------------------------------------------------------
