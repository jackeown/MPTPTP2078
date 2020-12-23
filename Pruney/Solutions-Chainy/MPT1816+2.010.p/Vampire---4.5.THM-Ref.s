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
% DateTime   : Thu Dec  3 13:19:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  270 (8948 expanded)
%              Number of leaves         :    5 (1513 expanded)
%              Depth                    :   53
%              Number of atoms          : 2141 (165684 expanded)
%              Number of equality atoms :   39 (6744 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3529)Refutation not found, incomplete strategy% (3529)------------------------------
% (3529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3529)Termination reason: Refutation not found, incomplete strategy

% (3529)Memory used [KB]: 11257
% (3529)Time elapsed: 0.151 s
% (3529)------------------------------
% (3529)------------------------------
fof(f1108,plain,(
    $false ),
    inference(global_subsumption,[],[f59,f970,f1107])).

fof(f1107,plain,(
    sP5(sK4,sK3,sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f1106,f874])).

fof(f874,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(duplicate_literal_removal,[],[f848])).

fof(f848,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f483,f829])).

fof(f829,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2) ),
    inference(forward_demodulation,[],[f826,f175])).

fof(f175,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) ),
    inference(resolution,[],[f157,f31])).

fof(f31,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
                       => ( ( r4_tsep_1(X0,X3,X4)
                            & k1_tsep_1(X0,X3,X4) = X0 )
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f157,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f156,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f155,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f155,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f154,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f154,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f153,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f153,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f152,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f151,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f151,plain,(
    ! [X2] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f150,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f150,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f144,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f144,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f37,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f826,plain,(
    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2) ),
    inference(resolution,[],[f825,f31])).

fof(f825,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f824,f42])).

fof(f824,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f823,f43])).

fof(f823,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f822,f44])).

fof(f822,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f821])).

fof(f821,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(resolution,[],[f149,f61])).

fof(f61,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f148,f38])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f147,f36])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f146,f41])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f145,f40])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f37,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f483,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f482,f38])).

fof(f482,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f481,f37])).

fof(f481,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f480,f36])).

fof(f480,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f479,f41])).

fof(f479,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f478,f40])).

fof(f478,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f472,f39])).

fof(f472,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f142,f166])).

fof(f166,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f142,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f140,f33])).

fof(f33,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f140,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f139,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f138,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f138,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f137,f35])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f137,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f136,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f135,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(subsumption_resolution,[],[f70,f43])).

fof(f70,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(X16,sK0,X17)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17))))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) ) ),
    inference(superposition,[],[f54,f32])).

fof(f32,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f1106,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | sP5(sK4,sK3,sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f1105,f876])).

fof(f876,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(duplicate_literal_removal,[],[f834])).

fof(f834,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(backward_demodulation,[],[f255,f829])).

fof(f255,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f254,f38])).

fof(f254,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f253,f37])).

fof(f253,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f252,f36])).

fof(f252,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f251,f41])).

fof(f251,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f250,f40])).

fof(f250,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f224,f39])).

fof(f224,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f118,f160])).

fof(f160,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f21,f28])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f118,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f116,f33])).

fof(f116,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f115,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f113,f35])).

fof(f113,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f112,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(subsumption_resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X10,X11] :
      ( ~ v5_pre_topc(X10,sK0,X11)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11)))) ) ),
    inference(superposition,[],[f51,f32])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1105,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | sP5(sK4,sK3,sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f1101,f875])).

fof(f875,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f844])).

fof(f844,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f411,f829])).

fof(f411,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f410,f38])).

fof(f410,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f409,f37])).

fof(f409,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f408,f36])).

fof(f408,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f407,f41])).

fof(f407,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f406,f40])).

fof(f406,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f390,f39])).

fof(f390,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(resolution,[],[f126,f164])).

fof(f164,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(resolution,[],[f22,f28])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f126,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f124,f33])).

fof(f124,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f123,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f122,f30])).

fof(f122,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f121,f35])).

fof(f121,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f120,f34])).

fof(f120,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(subsumption_resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X12,X13] :
      ( ~ v5_pre_topc(X12,sK0,X13)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13)))) ) ),
    inference(superposition,[],[f52,f32])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1101,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | sP5(sK4,sK3,sK2,sK1,sK0) ),
    inference(resolution,[],[f1045,f1030])).

fof(f1030,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(forward_demodulation,[],[f1029,f829])).

fof(f1029,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) ),
    inference(subsumption_resolution,[],[f1028,f38])).

fof(f1028,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f1027,f37])).

fof(f1027,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f1026,f36])).

fof(f1026,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f1025,f41])).

fof(f1025,plain,
    ( ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f1024,f40])).

fof(f1024,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f980,f39])).

fof(f980,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f970,f134])).

fof(f134,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f133,f42])).

fof(f133,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f132,f33])).

fof(f132,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f131,f31])).

fof(f131,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f130,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f129,f35])).

fof(f129,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f128,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f127,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(subsumption_resolution,[],[f69,f43])).

fof(f69,plain,(
    ! [X14,X15] :
      ( ~ v5_pre_topc(X14,sK0,X15)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) ) ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1045,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | sP5(X0,sK3,sK2,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f1044,f922])).

fof(f922,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(duplicate_literal_removal,[],[f897])).

fof(f897,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f447,f877])).

fof(f877,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f827,f176])).

fof(f176,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f157,f35])).

fof(f827,plain,(
    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2) ),
    inference(resolution,[],[f825,f35])).

fof(f447,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f446,f38])).

fof(f446,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f445,f37])).

fof(f445,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f444,f36])).

fof(f444,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f443,f41])).

fof(f443,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f442,f40])).

fof(f442,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f431,f39])).

fof(f431,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f110,f165])).

fof(f165,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f20,f28])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f110,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f108,f33])).

fof(f108,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f107,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f106,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f105,f35])).

fof(f105,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f103,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(X8,sK0,X9)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(superposition,[],[f50,f32])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1044,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | sP5(X0,sK3,sK2,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f1043,f924])).

fof(f924,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f883])).

fof(f883,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f219,f877])).

fof(f219,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f218,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f217,f37])).

fof(f217,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f216,f36])).

fof(f216,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f215,f41])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f214,f40])).

fof(f214,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f183,f39])).

fof(f183,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f86,f159])).

fof(f159,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f17,f28])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(subsumption_resolution,[],[f63,f43])).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK0,X3)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) ) ),
    inference(superposition,[],[f47,f32])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1043,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | sP5(X0,sK3,sK2,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f1040,f923])).

fof(f923,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f893])).

fof(f893,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f375,f877])).

fof(f375,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f374,f38])).

fof(f374,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f373,f37])).

fof(f373,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f372,f36])).

fof(f372,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f371,f41])).

fof(f371,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f370,f40])).

fof(f370,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f349,f39])).

fof(f349,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f94,f163])).

fof(f163,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f18,f28])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f93,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f92,f33])).

fof(f92,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f91,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f88,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(X4,sK0,X5)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) ) ),
    inference(superposition,[],[f48,f32])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1040,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | sP5(X0,sK3,sK2,sK1,sK0) ) ),
    inference(resolution,[],[f1002,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1002,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    inference(forward_demodulation,[],[f1001,f877])).

fof(f1001,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) ),
    inference(subsumption_resolution,[],[f1000,f38])).

fof(f1000,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f999,f37])).

fof(f999,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f998,f36])).

fof(f998,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f997,f41])).

fof(f997,plain,
    ( ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f996,f40])).

fof(f996,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f976,f39])).

fof(f976,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f970,f102])).

fof(f102,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f100,f33])).

fof(f100,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(subsumption_resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X6,X7] :
      ( ~ v5_pre_topc(X6,sK0,X7)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    inference(superposition,[],[f49,f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f970,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f969,f161])).

fof(f161,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f19,f28])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f969,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f968,f877])).

fof(f968,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f967,f922])).

fof(f967,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f966,f877])).

fof(f966,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f965,f923])).

fof(f965,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f964,f877])).

fof(f964,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f963,f924])).

fof(f963,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f962,f877])).

fof(f962,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f961,f162])).

fof(f162,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f23,f28])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f961,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f960,f874])).

fof(f960,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f959,f875])).

fof(f959,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f958,f876])).

fof(f958,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f957,f38])).

fof(f957,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f956,f37])).

fof(f956,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f955,f36])).

fof(f955,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f954,f41])).

fof(f954,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f953,f40])).

fof(f953,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f952,f39])).

fof(f952,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f78,f829])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f76,f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f75,f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f74,f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f62,f43])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f38])).

fof(f58,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f57,f37])).

fof(f57,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f25,f36])).

fof(f25,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (3521)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.48  % (3544)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.48  % (3544)Refutation not found, incomplete strategy% (3544)------------------------------
% 0.22/0.48  % (3544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3544)Memory used [KB]: 10746
% 0.22/0.48  % (3544)Time elapsed: 0.031 s
% 0.22/0.48  % (3544)------------------------------
% 0.22/0.48  % (3544)------------------------------
% 0.22/0.50  % (3524)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (3529)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (3522)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (3528)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3525)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (3531)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (3523)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (3541)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (3526)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (3538)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (3532)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (3533)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (3542)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (3527)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (3528)Refutation not found, incomplete strategy% (3528)------------------------------
% 0.22/0.52  % (3528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3528)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3528)Memory used [KB]: 6524
% 0.22/0.52  % (3528)Time elapsed: 0.088 s
% 0.22/0.52  % (3528)------------------------------
% 0.22/0.52  % (3528)------------------------------
% 0.22/0.52  % (3535)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (3537)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (3536)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (3524)Refutation not found, incomplete strategy% (3524)------------------------------
% 0.22/0.53  % (3524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3524)Memory used [KB]: 10618
% 0.22/0.53  % (3524)Time elapsed: 0.110 s
% 0.22/0.53  % (3524)------------------------------
% 0.22/0.53  % (3524)------------------------------
% 0.22/0.53  % (3540)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (3534)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (3539)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (3530)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (3543)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.54  % (3541)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.55  % (3529)Refutation not found, incomplete strategy% (3529)------------------------------
% 0.22/0.55  % (3529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3529)Memory used [KB]: 11257
% 0.22/0.55  % (3529)Time elapsed: 0.151 s
% 0.22/0.55  % (3529)------------------------------
% 0.22/0.55  % (3529)------------------------------
% 0.22/0.55  fof(f1108,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(global_subsumption,[],[f59,f970,f1107])).
% 0.22/0.55  fof(f1107,plain,(
% 0.22/0.55    sP5(sK4,sK3,sK2,sK1,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1106,f874])).
% 0.22/0.55  fof(f874,plain,(
% 0.22/0.55    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f848])).
% 0.22/0.55  fof(f848,plain,(
% 0.22/0.55    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(backward_demodulation,[],[f483,f829])).
% 0.22/0.55  fof(f829,plain,(
% 0.22/0.55    k2_tmap_1(sK0,sK1,sK2,sK4) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f826,f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4))),
% 0.22/0.55    inference(resolution,[],[f157,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    m1_pre_topc(sK4,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f5])).
% 0.22/0.55  fof(f5,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f156,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f155,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f154,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ( ! [X2] : (~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    l1_pre_topc(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X2] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f152,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    v2_pre_topc(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ( ! [X2] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f151,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ~v2_struct_0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X2] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f150,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X2] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f144,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    v2_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.22/0.55    inference(resolution,[],[f37,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f826,plain,(
% 0.22/0.55    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)),
% 0.22/0.55    inference(resolution,[],[f825,f31])).
% 0.22/0.55  fof(f825,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f824,f42])).
% 0.22/0.55  fof(f824,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f823,f43])).
% 0.22/0.55  fof(f823,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f822,f44])).
% 0.22/0.55  fof(f822,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f821])).
% 0.22/0.55  fof(f821,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.55    inference(resolution,[],[f149,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    m1_pre_topc(sK0,sK0)),
% 0.22/0.55    inference(resolution,[],[f44,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f148,f38])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f36])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f146,f41])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f145,f40])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f143,f39])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.55    inference(resolution,[],[f37,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.55  fof(f483,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f482,f38])).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f481,f37])).
% 0.22/0.55  fof(f481,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f480,f36])).
% 0.22/0.55  fof(f480,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f479,f41])).
% 0.22/0.55  fof(f479,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f478,f40])).
% 0.22/0.55  fof(f478,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f472,f39])).
% 0.22/0.55  fof(f472,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f142,f166])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f24,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    sP5(sK4,sK3,sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f141,f42])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f140,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f139,f31])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f138,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ~v2_struct_0(sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f137,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    m1_pre_topc(sK3,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f136,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ~v2_struct_0(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f135,f44])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | ~l1_pre_topc(sK0) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f70,f43])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X17,X16] : (~v5_pre_topc(X16,sK0,X17) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X17) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X17,sK0,sK4,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X17)))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | v2_struct_0(sK0) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))) )),
% 0.22/0.55    inference(superposition,[],[f54,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).
% 0.22/0.55  fof(f1106,plain,(
% 0.22/0.55    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | sP5(sK4,sK3,sK2,sK1,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1105,f876])).
% 0.22/0.55  fof(f876,plain,(
% 0.22/0.55    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f834])).
% 0.22/0.55  fof(f834,plain,(
% 0.22/0.55    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(backward_demodulation,[],[f255,f829])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f254,f38])).
% 0.22/0.55  fof(f254,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f253,f37])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f252,f36])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f251,f41])).
% 0.22/0.55  fof(f251,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f250,f40])).
% 0.22/0.55  fof(f250,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(subsumption_resolution,[],[f224,f39])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(resolution,[],[f118,f160])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.55    inference(resolution,[],[f21,f28])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_1(k2_tmap_1(X0,X1,X2,X4))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f117,f42])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f116,f33])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f115,f31])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f114,f30])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f113,f35])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f112,f34])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f111,f44])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | ~l1_pre_topc(sK0) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f67,f43])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X10,X11] : (~v5_pre_topc(X10,sK0,X11) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X11,sK0,sK4,X10)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X11)) | v2_struct_0(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X11))))) )),
% 0.22/0.55    inference(superposition,[],[f51,f32])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1105,plain,(
% 0.22/0.55    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | sP5(sK4,sK3,sK2,sK1,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1101,f875])).
% 0.22/0.55  fof(f875,plain,(
% 0.22/0.55    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f844])).
% 0.22/0.55  fof(f844,plain,(
% 0.22/0.55    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(backward_demodulation,[],[f411,f829])).
% 0.22/0.55  fof(f411,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f410,f38])).
% 0.22/0.55  fof(f410,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f409,f37])).
% 0.22/0.55  fof(f409,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f408,f36])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f407,f41])).
% 0.22/0.55  fof(f407,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f406,f40])).
% 0.22/0.55  fof(f406,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f390,f39])).
% 0.22/0.55  fof(f390,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f126,f164])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f22,f28])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f125,f42])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f124,f33])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f123,f31])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f122,f30])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f121,f35])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f120,f34])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f119,f44])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | ~l1_pre_topc(sK0) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f68,f43])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,X13) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X13,sK0,sK4,X12),u1_struct_0(sK4),u1_struct_0(X13)) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(sK0),u1_struct_0(X13)) | v2_struct_0(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X13))))) )),
% 0.22/0.55    inference(superposition,[],[f52,f32])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1101,plain,(
% 0.22/0.55    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | sP5(sK4,sK3,sK2,sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f1045,f1030])).
% 0.22/0.55  fof(f1030,plain,(
% 0.22/0.55    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f1029,f829])).
% 0.22/0.55  fof(f1029,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1028,f38])).
% 0.22/0.55  fof(f1028,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f1027,f37])).
% 0.22/0.55  fof(f1027,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f1026,f36])).
% 0.22/0.55  fof(f1026,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f1025,f41])).
% 0.22/0.55  fof(f1025,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f1024,f40])).
% 0.22/0.55  fof(f1024,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f980,f39])).
% 0.22/0.55  fof(f980,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK4,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f970,f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f42])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f33])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f31])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f130,f30])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f129,f35])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f128,f34])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f127,f44])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | ~l1_pre_topc(sK0) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f69,f43])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X14,X15] : (~v5_pre_topc(X14,sK0,X15) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X15,sK0,sK4,X14),sK4,X15) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(sK0),u1_struct_0(X15)) | v2_struct_0(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))) )),
% 0.22/0.55    inference(superposition,[],[f53,f32])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1045,plain,(
% 0.22/0.55    ( ! [X0] : (~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | sP5(X0,sK3,sK2,sK1,sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f1044,f922])).
% 0.22/0.55  fof(f922,plain,(
% 0.22/0.55    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f897])).
% 0.22/0.55  fof(f897,plain,(
% 0.22/0.55    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(backward_demodulation,[],[f447,f877])).
% 0.22/0.55  fof(f877,plain,(
% 0.22/0.55    k2_tmap_1(sK0,sK1,sK2,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f827,f176])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3))),
% 0.22/0.55    inference(resolution,[],[f157,f35])).
% 0.22/0.55  fof(f827,plain,(
% 0.22/0.55    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)),
% 0.22/0.55    inference(resolution,[],[f825,f35])).
% 0.22/0.55  fof(f447,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f446,f38])).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f445,f37])).
% 0.22/0.55  fof(f445,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f444,f36])).
% 0.22/0.55  fof(f444,plain,(
% 0.22/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f443,f41])).
% 0.22/0.55  fof(f443,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f442,f40])).
% 0.22/0.55  fof(f442,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f431,f39])).
% 0.22/0.55  fof(f431,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f110,f165])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f20,f28])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f109,f42])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f33])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f107,f31])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f106,f30])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f105,f35])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f104,f34])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f103,f44])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f66,f43])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | m1_subset_1(k3_tmap_1(sK0,X9,sK0,sK3,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK0),u1_struct_0(X9)) | v2_struct_0(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.22/0.55    inference(superposition,[],[f50,f32])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1044,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | sP5(X0,sK3,sK2,sK1,sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f1043,f924])).
% 0.22/0.55  fof(f924,plain,(
% 0.22/0.55    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f883])).
% 0.22/0.55  fof(f883,plain,(
% 0.22/0.55    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(backward_demodulation,[],[f219,f877])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f218,f38])).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f217,f37])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f216,f36])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f215,f41])).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f214,f40])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f183,f39])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(resolution,[],[f86,f159])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(resolution,[],[f17,f28])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f85,f42])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f84,f33])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f83,f31])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f82,f30])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f81,f35])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f80,f34])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f79,f44])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f63,f43])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~v5_pre_topc(X2,sK0,X3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X3,sK0,sK3,X2)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))) )),
% 0.22/0.55    inference(superposition,[],[f47,f32])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1043,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | sP5(X0,sK3,sK2,sK1,sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f1040,f923])).
% 0.22/0.55  fof(f923,plain,(
% 0.22/0.55    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f893])).
% 0.22/0.55  fof(f893,plain,(
% 0.22/0.55    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(backward_demodulation,[],[f375,f877])).
% 0.22/0.55  fof(f375,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f374,f38])).
% 0.22/0.55  fof(f374,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f373,f37])).
% 0.22/0.55  fof(f373,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f372,f36])).
% 0.22/0.55  fof(f372,plain,(
% 0.22/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f371,f41])).
% 0.22/0.55  fof(f371,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f370,f40])).
% 0.22/0.55  fof(f370,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f349,f39])).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f94,f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    v5_pre_topc(sK2,sK0,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.55    inference(resolution,[],[f18,f28])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f93,f42])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f92,f33])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f91,f31])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f90,f30])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f89,f35])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f88,f34])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f87,f44])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f64,f43])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~v5_pre_topc(X4,sK0,X5) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_2(k3_tmap_1(sK0,X5,sK0,sK3,X4),u1_struct_0(sK3),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))) )),
% 0.22/0.55    inference(superposition,[],[f48,f32])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f1040,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | sP5(X0,sK3,sK2,sK1,sK0)) )),
% 0.22/0.55    inference(resolution,[],[f1002,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | sP5(X4,X3,X2,X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f1002,plain,(
% 0.22/0.55    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f1001,f877])).
% 0.22/0.55  fof(f1001,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1000,f38])).
% 0.22/0.55  fof(f1000,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f999,f37])).
% 0.22/0.55  fof(f999,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f998,f36])).
% 0.22/0.55  fof(f998,plain,(
% 0.22/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f997,f41])).
% 0.22/0.55  fof(f997,plain,(
% 0.22/0.55    ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f996,f40])).
% 0.22/0.55  fof(f996,plain,(
% 0.22/0.55    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f976,f39])).
% 0.22/0.55  fof(f976,plain,(
% 0.22/0.55    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(resolution,[],[f970,f102])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f101,f42])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f100,f33])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f99,f31])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f98,f30])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f97,f35])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f96,f34])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f95,f44])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f65,f43])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_pre_topc(X6,sK0,X7) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v5_pre_topc(k3_tmap_1(sK0,X7,sK0,sK3,X6),sK3,X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X7)) | v2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))) )),
% 0.22/0.55    inference(superposition,[],[f49,f32])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f970,plain,(
% 0.22/0.56    v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f969,f161])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f19,f28])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f969,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f968,f877])).
% 0.22/0.56  fof(f968,plain,(
% 0.22/0.56    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f967,f922])).
% 0.22/0.56  fof(f967,plain,(
% 0.22/0.56    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f966,f877])).
% 0.22/0.56  fof(f966,plain,(
% 0.22/0.56    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f965,f923])).
% 0.22/0.56  fof(f965,plain,(
% 0.22/0.56    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f964,f877])).
% 0.22/0.56  fof(f964,plain,(
% 0.22/0.56    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f963,f924])).
% 0.22/0.56  fof(f963,plain,(
% 0.22/0.56    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f962,f877])).
% 0.22/0.56  fof(f962,plain,(
% 0.22/0.56    ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f961,f162])).
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f23,f28])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f961,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f960,f874])).
% 0.22/0.56  fof(f960,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f959,f875])).
% 0.22/0.56  fof(f959,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f958,f876])).
% 0.22/0.56  fof(f958,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f957,f38])).
% 0.22/0.56  fof(f957,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f956,f37])).
% 0.22/0.56  fof(f956,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f955,f36])).
% 0.22/0.56  fof(f955,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f954,f41])).
% 0.22/0.56  fof(f954,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f953,f40])).
% 0.22/0.56  fof(f953,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f952,f39])).
% 0.22/0.56  fof(f952,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f78,f829])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f77,f42])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f76,f33])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f75,f31])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f74,f30])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f73,f35])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f72,f34])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f71,f44])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f62,f43])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(sK0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.56    inference(superposition,[],[f46,f32])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f58,f38])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f57,f37])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f25,f36])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (3541)------------------------------
% 0.22/0.56  % (3541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (3541)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (3541)Memory used [KB]: 6652
% 0.22/0.56  % (3541)Time elapsed: 0.123 s
% 0.22/0.56  % (3541)------------------------------
% 0.22/0.56  % (3541)------------------------------
% 0.22/0.56  % (3520)Success in time 0.193 s
%------------------------------------------------------------------------------
