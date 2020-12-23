%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 (1853 expanded)
%              Number of leaves         :   14 ( 327 expanded)
%              Depth                    :   42
%              Number of atoms          :  995 (19440 expanded)
%              Number of equality atoms :   17 (1014 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(subsumption_resolution,[],[f473,f226])).

fof(f226,plain,(
    ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f87,f225])).

fof(f225,plain,(
    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f224,f88])).

fof(f88,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f44,f47])).

fof(f47,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f44,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f224,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f223,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f223,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f222,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f222,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f219,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f219,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(resolution,[],[f139,f86])).

fof(f86,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK1,sK0,sK2,X1)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f136,plain,(
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
    inference(subsumption_resolution,[],[f135,f57])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f135,plain,(
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
    inference(subsumption_resolution,[],[f134,f56])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f134,plain,(
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
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,(
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
    inference(subsumption_resolution,[],[f132,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f132,plain,(
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
    inference(subsumption_resolution,[],[f131,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,(
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
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f87,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f45,f47])).

fof(f45,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f473,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f472,f59])).

fof(f472,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f471,f328])).

fof(f328,plain,(
    r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f327,f55])).

fof(f327,plain,
    ( r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f326,f48])).

fof(f326,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f325,f57])).

fof(f325,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f313,f56])).

fof(f313,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f303,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_tarski(sK6(X0,X1,X2),X2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f65,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK6(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f303,plain,(
    m1_connsp_2(u1_struct_0(sK3),sK1,sK4) ),
    inference(subsumption_resolution,[],[f282,f302])).

fof(f302,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f228,f207])).

fof(f207,plain,(
    m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f206,f49])).

fof(f206,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f205,f86])).

fof(f205,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f204,f97])).

fof(f97,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f96,f57])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f61,f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f204,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f186,f103])).

fof(f103,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f186,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f118,f78])).

fof(f118,plain,(
    m1_connsp_2(sK7(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f117,plain,
    ( v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f116,f97])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f112,f103])).

fof(f112,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK4),sK3,sK4) ),
    inference(resolution,[],[f79,f86])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f228,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f211,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f211,plain,(
    r2_hidden(sK4,sK7(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f210,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(sK4,sK7(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f209,f86])).

fof(f209,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK7(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f208,f97])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK7(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f187,f103])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | r2_hidden(sK4,sK7(sK3,sK4)) ),
    inference(resolution,[],[f118,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f68,f78])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f282,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f281,f48])).

fof(f281,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f151,f99])).

fof(f99,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f77,f86])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f151,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X4) ) ),
    inference(subsumption_resolution,[],[f150,f110])).

fof(f110,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(subsumption_resolution,[],[f109,f51])).

fof(f109,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f108,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f107,f57])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

% (7605)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f150,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | ~ r2_hidden(X4,u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X4) ) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f149,plain,(
    ! [X4] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | ~ r2_hidden(X4,u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X4) ) ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | ~ r2_hidden(X4,u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X4) ) ),
    inference(subsumption_resolution,[],[f142,f56])).

fof(f142,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | ~ r2_hidden(X4,u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X4) ) ),
    inference(resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f105,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f104,f57])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f62,f51])).

fof(f471,plain,
    ( ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f470,f324])).

fof(f324,plain,(
    r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f323,f55])).

fof(f323,plain,
    ( r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f322,f48])).

fof(f322,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f321,f57])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f312,f56])).

fof(f312,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f303,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,sK6(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f66,f78])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,sK6(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f470,plain,
    ( ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f469,f86])).

fof(f469,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f468,f48])).

fof(f468,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f467,f58])).

fof(f467,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f466,f51])).

fof(f466,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f465,f49])).

fof(f465,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f464,f54])).

fof(f464,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f463,f53])).

fof(f463,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f462,f52])).

fof(f462,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f461,f60])).

fof(f461,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(resolution,[],[f378,f225])).

fof(f378,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3)))
      | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3))
      | ~ v2_pre_topc(X1)
      | r1_tmap_1(sK1,X1,X2,X4) ) ),
    inference(subsumption_resolution,[],[f377,f332])).

fof(f332,plain,(
    v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) ),
    inference(subsumption_resolution,[],[f331,f55])).

fof(f331,plain,
    ( v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f330,f48])).

fof(f330,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f329,f57])).

fof(f329,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f314,f56])).

fof(f314,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f303,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v3_pre_topc(sK6(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f64,f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f377,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
      | ~ r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3)))
      | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
      | r1_tmap_1(sK1,X1,X2,X4) ) ),
    inference(subsumption_resolution,[],[f376,f57])).

fof(f376,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
      | ~ r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3)))
      | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
      | r1_tmap_1(sK1,X1,X2,X4) ) ),
    inference(subsumption_resolution,[],[f375,f56])).

fof(f375,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
      | ~ r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3)))
      | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
      | r1_tmap_1(sK1,X1,X2,X4) ) ),
    inference(subsumption_resolution,[],[f372,f55])).

fof(f372,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)
      | ~ r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3)))
      | ~ r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
      | r1_tmap_1(sK1,X1,X2,X4) ) ),
    inference(resolution,[],[f320,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
      | v2_struct_0(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f320,plain,(
    m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f319,f55])).

fof(f319,plain,
    ( m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f318,f48])).

fof(f318,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f317,f57])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f311,f56])).

fof(f311,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f303,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f78])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (7603)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (7611)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (7598)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (7618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (7599)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (7600)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7613)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (7610)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7614)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (7611)Refutation not found, incomplete strategy% (7611)------------------------------
% 0.21/0.49  % (7611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7608)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (7602)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (7606)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (7616)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (7615)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (7611)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7611)Memory used [KB]: 1791
% 0.21/0.49  % (7611)Time elapsed: 0.077 s
% 0.21/0.49  % (7611)------------------------------
% 0.21/0.49  % (7611)------------------------------
% 0.21/0.50  % (7615)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f474,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f473,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f224,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    sK4 = sK5),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f219,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    inference(resolution,[],[f139,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f46,f47])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(X0) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f138,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f136,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f135,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f133,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f131,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f81,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(forward_demodulation,[],[f45,f47])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f473,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f472,f59])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f471,f328])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3))),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f55])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f326,f48])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f325,f57])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f313,f56])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 0.21/0.50    inference(resolution,[],[f303,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tarski(sK6(X0,X1,X2),X2) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f65,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK6(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    m1_connsp_2(u1_struct_0(sK3),sK1,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f282,f302])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    inference(resolution,[],[f228,f207])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f49])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f86])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f204,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    l1_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f96,f57])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.21/0.50    inference(resolution,[],[f61,f51])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    v2_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f102,f56])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f57])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.21/0.50    inference(resolution,[],[f74,f51])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(resolution,[],[f118,f78])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    m1_connsp_2(sK7(sK3,sK4),sK3,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f49])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK4),sK3,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f116,f97])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK4),sK3,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f103])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK4),sK3,sK4)),
% 0.21/0.50    inference(resolution,[],[f79,f86])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK7(X0,X1),X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK7(sK3,sK4),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f211,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    r2_hidden(sK4,sK7(sK3,sK4))),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f49])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    v2_struct_0(sK3) | r2_hidden(sK4,sK7(sK3,sK4))),
% 0.21/0.50    inference(subsumption_resolution,[],[f209,f86])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK7(sK3,sK4))),
% 0.21/0.50    inference(subsumption_resolution,[],[f208,f97])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK7(sK3,sK4))),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f103])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | r2_hidden(sK4,sK7(sK3,sK4))),
% 0.21/0.50    inference(resolution,[],[f118,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f68,f78])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    inference(subsumption_resolution,[],[f281,f48])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    inference(resolution,[],[f151,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    r2_hidden(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    inference(resolution,[],[f77,f86])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK1)) | m1_connsp_2(u1_struct_0(sK3),sK1,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f51])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f56])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f57])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(resolution,[],[f90,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_tsep_1(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.50  % (7605)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X4,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f55])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X4] : (v2_struct_0(sK1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X4,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f57])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X4] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X4,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f56])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ( ! [X4] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X4,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X4)) )),
% 0.21/0.50    inference(resolution,[],[f105,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f104,f57])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(resolution,[],[f62,f51])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f470,f324])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f323,f55])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f322,f48])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f321,f57])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f312,f56])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(resolution,[],[f303,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,sK6(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f78])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,sK6(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f469,f86])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f468,f48])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f467,f58])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f466,f51])).
% 0.21/0.50  fof(f466,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f465,f49])).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f464,f54])).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f463,f53])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f462,f52])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f461,f60])).
% 0.21/0.50  fof(f461,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(resolution,[],[f378,f225])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3)) | ~v2_pre_topc(X1) | r1_tmap_1(sK1,X1,X2,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f377,f332])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f55])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f48])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f57])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f314,f56])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | v2_struct_0(sK1)),
% 0.21/0.50    inference(resolution,[],[f303,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v3_pre_topc(sK6(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f64,f78])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | ~r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3)) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4) | r1_tmap_1(sK1,X1,X2,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f376,f57])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | ~r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3)) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4) | r1_tmap_1(sK1,X1,X2,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f375,f56])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | ~r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3)) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4) | r1_tmap_1(sK1,X1,X2,X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f372,f55])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X1) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v3_pre_topc(sK6(sK1,sK4,u1_struct_0(sK3)),sK1) | ~r2_hidden(X4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r1_tarski(sK6(sK1,sK4,u1_struct_0(sK3)),u1_struct_0(X3)) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4) | r1_tmap_1(sK1,X1,X2,X4)) )),
% 0.21/0.50    inference(resolution,[],[f320,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.50    inference(equality_resolution,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f319,f55])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f318,f48])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f317,f57])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f311,f56])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | m1_subset_1(sK6(sK1,sK4,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.21/0.50    inference(resolution,[],[f303,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f78])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (7615)------------------------------
% 0.21/0.50  % (7615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7615)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (7615)Memory used [KB]: 1918
% 0.21/0.50  % (7615)Time elapsed: 0.088 s
% 0.21/0.50  % (7615)------------------------------
% 0.21/0.50  % (7615)------------------------------
% 0.21/0.50  % (7599)Refutation not found, incomplete strategy% (7599)------------------------------
% 0.21/0.50  % (7599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7599)Memory used [KB]: 10746
% 0.21/0.50  % (7599)Time elapsed: 0.073 s
% 0.21/0.50  % (7599)------------------------------
% 0.21/0.50  % (7599)------------------------------
% 0.21/0.51  % (7604)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (7607)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (7597)Success in time 0.154 s
%------------------------------------------------------------------------------
