%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  269 (4617 expanded)
%              Number of leaves         :    6 ( 783 expanded)
%              Depth                    :   56
%              Number of atoms          : 2213 (88692 expanded)
%              Number of equality atoms :   39 (3476 expanded)
%              Maximal formula depth    :   28 (  10 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(subsumption_resolution,[],[f707,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(flattening,[],[f8])).

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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_tmap_1)).

fof(f707,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f706,f35])).

fof(f35,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f706,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f705,f34])).

fof(f34,plain,(
    v1_tsep_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f705,plain,
    ( ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f704,f39])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f704,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f703,f38])).

fof(f38,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f703,plain,
    ( ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f702,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f702,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f701,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f701,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f700,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
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
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

fof(f700,plain,(
    ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f699,f301])).

fof(f301,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f300,f72])).

fof(f72,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f23,f31])).

fof(f31,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f300,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f299,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f299,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f298,f41])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f298,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f297,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f297,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f296,f45])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f296,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f295,f44])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f295,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f287,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f287,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f284,f132])).

fof(f132,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f129,f98])).

fof(f98,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f84,f39])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f77,f48])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f60,f42])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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

fof(f129,plain,(
    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2) ),
    inference(resolution,[],[f127,f39])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f111,f41])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f108,f44])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f50,f42])).

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
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f284,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f283,f46])).

fof(f283,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f282,f35])).

fof(f282,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f281,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f281,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f280,f39])).

fof(f280,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f279,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f279,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f278,f48])).

fof(f278,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f259,f47])).

fof(f259,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f55,f36])).

fof(f36,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f699,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(forward_demodulation,[],[f698,f132])).

fof(f698,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f697,f204])).

fof(f204,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f203,f68])).

fof(f68,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f22,f31])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f203,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f202,f42])).

fof(f202,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f201,f41])).

fof(f201,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f200,f40])).

fof(f200,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f199,f45])).

fof(f199,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f198,f44])).

fof(f198,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f197,f43])).

fof(f197,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f196,f132])).

fof(f196,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f195,f46])).

fof(f195,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f194,f35])).

fof(f194,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f193,f33])).

fof(f193,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f192,f39])).

fof(f192,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f191,f37])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f190,f48])).

fof(f190,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f189,f47])).

fof(f189,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f54,f36])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f697,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f696,f132])).

fof(f696,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f695,f236])).

fof(f236,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f235,f70])).

fof(f70,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f21,f31])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f235,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f234,f42])).

fof(f234,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f233,f41])).

fof(f233,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f232,f40])).

fof(f232,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f231,f45])).

fof(f231,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f230,f44])).

fof(f230,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f229,f43])).

fof(f229,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f228,f132])).

fof(f228,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f227,f46])).

fof(f227,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f226,f35])).

fof(f226,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f225,f33])).

fof(f225,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f224,f39])).

fof(f224,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f223,f37])).

fof(f223,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f222,f48])).

fof(f222,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f221,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f53,f36])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f695,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f694,f132])).

fof(f694,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f693,f172])).

fof(f172,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f171,f66])).

fof(f66,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f20,f31])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f171,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f170,f132])).

fof(f170,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f169,f41])).

fof(f169,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f168,f40])).

fof(f168,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f167,f45])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f166,f44])).

fof(f166,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f165,f43])).

fof(f165,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f164,f42])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f163,f46])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f35])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f33])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f39])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f37])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f48])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f47])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f52,f36])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f693,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f692,f132])).

fof(f692,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f691,f220])).

fof(f220,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f219,f69])).

fof(f69,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f26,f31])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f219,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f218,f42])).

fof(f218,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f217,f41])).

fof(f217,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f216,f40])).

fof(f216,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f215,f45])).

fof(f215,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f213,f43])).

fof(f213,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f212,f131])).

fof(f131,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2) ),
    inference(forward_demodulation,[],[f128,f97])).

fof(f97,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) ),
    inference(resolution,[],[f84,f35])).

fof(f128,plain,(
    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2) ),
    inference(resolution,[],[f127,f35])).

fof(f212,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f211,f46])).

fof(f211,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f210,f35])).

fof(f210,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f209,f33])).

fof(f209,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f208,f39])).

fof(f208,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f207,f37])).

fof(f207,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f206,f48])).

fof(f206,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f205,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f58,f36])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f691,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f690,f252])).

fof(f252,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f251,f71])).

fof(f71,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f25,f31])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f251,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f250,f42])).

fof(f250,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f249,f41])).

fof(f249,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f248,f40])).

fof(f248,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f247,f45])).

fof(f247,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f246,f44])).

fof(f246,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f245,f43])).

fof(f245,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f244,f131])).

fof(f244,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f243,f46])).

fof(f243,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f242,f35])).

fof(f242,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f241,f33])).

fof(f241,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f240,f39])).

fof(f240,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f239,f37])).

fof(f239,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f238,f48])).

fof(f238,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f237,f47])).

fof(f237,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f57,f36])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f690,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f689,f188])).

fof(f188,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f187,f67])).

fof(f67,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f24,f31])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f187,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f186,f131])).

fof(f186,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f185,f41])).

fof(f185,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f183,f45])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f182,f44])).

fof(f182,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f181,f43])).

fof(f181,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f180,f42])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f179,f46])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f35])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f37])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f47])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f56,f36])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f689,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f688,f418])).

fof(f418,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f417,f73])).

fof(f73,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f27,f31])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X3,X2,X1,X0)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f417,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f416,f42])).

fof(f416,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f415,f41])).

fof(f415,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f414,f40])).

fof(f414,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f413,f45])).

fof(f413,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f412,f44])).

fof(f412,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f404,f43])).

fof(f404,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f401,f131])).

fof(f401,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f400,f46])).

fof(f400,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f399,f35])).

fof(f399,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f398,f33])).

fof(f398,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f397,f39])).

fof(f397,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f396,f37])).

fof(f396,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f395,f48])).

fof(f395,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f372,f47])).

fof(f372,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f59,f36])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f688,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f687,f597])).

fof(f597,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(resolution,[],[f593,f64])).

fof(f64,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f63,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f62,f41])).

fof(f62,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f28,f40])).

fof(f28,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f593,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f592,f172])).

fof(f592,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f591,f236])).

fof(f591,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f590,f204])).

fof(f590,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f585])).

fof(f585,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ r4_tsep_1(sK0,sK3,sK4) ),
    inference(resolution,[],[f499,f301])).

fof(f499,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2))
      | sP5(sK4,X2,sK2,sK1,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f498,f220])).

fof(f498,plain,(
    ! [X2] :
      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2))
      | sP5(sK4,X2,sK2,sK1,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f497,f252])).

fof(f497,plain,(
    ! [X2] :
      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2))
      | sP5(sK4,X2,sK2,sK1,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f489,f188])).

fof(f489,plain,(
    ! [X2] :
      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2))
      | sP5(sK4,X2,sK2,sK1,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4) ) ),
    inference(resolution,[],[f19,f418])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f687,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f686,f42])).

fof(f686,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f685,f41])).

fof(f685,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f684,f40])).

fof(f684,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f683,f45])).

fof(f683,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f682,f44])).

fof(f682,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f680,f43])).

fof(f680,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f678,f131])).

fof(f678,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f677,f46])).

fof(f677,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f676,f35])).

fof(f676,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f675,f33])).

fof(f675,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f674,f39])).

fof(f674,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f673,f37])).

fof(f673,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f672,f48])).

fof(f672,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f669,f47])).

fof(f669,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
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
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(superposition,[],[f51,f36])).

% (13041)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | v2_struct_0(X0)
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:50:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (13036)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.46  % (13035)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.46  % (13040)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.47  % (13028)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.47  % (13039)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.47  % (13033)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.47  % (13042)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.47  % (13026)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.48  % (13026)Refutation not found, incomplete strategy% (13026)------------------------------
% 0.22/0.48  % (13026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13026)Memory used [KB]: 10618
% 0.22/0.48  % (13026)Time elapsed: 0.076 s
% 0.22/0.48  % (13026)------------------------------
% 0.22/0.48  % (13026)------------------------------
% 0.22/0.48  % (13034)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.48  % (13032)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.48  % (13043)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.48  % (13031)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.48  % (13027)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.48  % (13036)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f708,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f707,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_tmap_1)).
% 0.22/0.48  fof(f707,plain,(
% 0.22/0.48    v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f706,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    m1_pre_topc(sK4,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f706,plain,(
% 0.22/0.48    ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f705,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v1_tsep_1(sK4,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f705,plain,(
% 0.22/0.48    ~v1_tsep_1(sK4,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f704,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    m1_pre_topc(sK3,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f704,plain,(
% 0.22/0.48    ~m1_pre_topc(sK3,sK0) | ~v1_tsep_1(sK4,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f703,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v1_tsep_1(sK3,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f703,plain,(
% 0.22/0.48    ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_tsep_1(sK4,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f702,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f702,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_tsep_1(sK4,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f701,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f701,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_tsep_1(sK4,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f700,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).
% 0.22/0.48  fof(f700,plain,(
% 0.22/0.48    ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f699,f301])).
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f300,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f23,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    sP5(sK4,sK3,sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f299,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f299,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f298,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f298,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f297,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f297,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f296,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    l1_pre_topc(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f296,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f295,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    v2_pre_topc(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f287,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~v2_struct_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f287,plain,(
% 0.22/0.48    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(superposition,[],[f284,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k2_tmap_1(sK0,sK1,sK2,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)),
% 0.22/0.48    inference(forward_demodulation,[],[f129,f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3))),
% 0.22/0.48    inference(resolution,[],[f84,f39])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f46])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f41])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f40])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f45])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f79,f44])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f78,f43])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f48])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f47])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 0.22/0.48    inference(resolution,[],[f60,f42])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)),
% 0.22/0.48    inference(resolution,[],[f127,f39])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f126,f46])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f47])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f48])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f112,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f111,f41])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f110,f40])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f109,f45])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f44])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f105,f43])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) )),
% 0.22/0.48    inference(resolution,[],[f50,f42])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.48  fof(f284,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f283,f46])).
% 0.22/0.48  fof(f283,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f282,f35])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f281,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ~v2_struct_0(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f280,f39])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f279,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ~v2_struct_0(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f48])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f259,f47])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f55,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).
% 0.22/0.49  fof(f699,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(forward_demodulation,[],[f698,f132])).
% 0.22/0.49  fof(f698,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f697,f204])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f203,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f22,f31])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f202,f42])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f201,f41])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f200,f40])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f199,f45])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f198,f44])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f197,f43])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(superposition,[],[f196,f132])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f195,f46])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f194,f35])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f193,f33])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f192,f39])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f191,f37])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f190,f48])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f189,f47])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f54,f36])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f697,plain,(
% 0.22/0.49    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(forward_demodulation,[],[f696,f132])).
% 0.22/0.49  fof(f696,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f695,f236])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f235,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f21,f31])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f234,f42])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f233,f41])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f232,f40])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f231,f45])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f230,f44])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f43])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(superposition,[],[f228,f132])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f227,f46])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f35])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f225,f33])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f224,f39])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f223,f37])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f48])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f221,f47])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f53,f36])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f695,plain,(
% 0.22/0.49    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(forward_demodulation,[],[f694,f132])).
% 0.22/0.49  fof(f694,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f693,f172])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f171,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f20,f31])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f170,f132])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f169,f41])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f168,f40])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f167,f45])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f44])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f165,f43])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f164,f42])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f163,f46])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f162,f35])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f161,f33])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f160,f39])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f159,f37])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f158,f48])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f157,f47])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(superposition,[],[f52,f36])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f693,plain,(
% 0.22/0.49    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(forward_demodulation,[],[f692,f132])).
% 0.22/0.49  fof(f692,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f691,f220])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f219,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f26,f31])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f218,f42])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f217,f41])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f216,f40])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f215,f45])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f214,f44])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f213,f43])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(superposition,[],[f212,f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    k2_tmap_1(sK0,sK1,sK2,sK4) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)),
% 0.22/0.49    inference(forward_demodulation,[],[f128,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4))),
% 0.22/0.49    inference(resolution,[],[f84,f35])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f127,f35])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f211,f46])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f210,f35])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f209,f33])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f208,f39])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f37])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f48])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f205,f47])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f58,f36])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f691,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f690,f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f251,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f25,f31])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f250,f42])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f249,f41])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f248,f40])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f247,f45])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f246,f44])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f245,f43])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(superposition,[],[f244,f131])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f46])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f242,f35])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f241,f33])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f39])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f239,f37])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f238,f48])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f237,f47])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f57,f36])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f690,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f689,f188])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f187,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f24,f31])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | v1_funct_1(k2_tmap_1(X0,X1,X2,X4))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f186,f131])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f185,f41])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f184,f40])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f183,f45])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f182,f44])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f181,f43])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK4,sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f180,f42])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f179,f46])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f178,f35])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f177,f33])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f176,f39])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f175,f37])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f174,f48])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f173,f47])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(superposition,[],[f56,f36])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f689,plain,(
% 0.22/0.49    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f688,f418])).
% 0.22/0.49  fof(f418,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f417,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f27,f31])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X3,X2,X1,X0) | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f417,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f416,f42])).
% 0.22/0.49  fof(f416,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f415,f41])).
% 0.22/0.49  fof(f415,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f414,f40])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f413,f45])).
% 0.22/0.49  fof(f413,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f412,f44])).
% 0.22/0.49  fof(f412,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f404,f43])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(superposition,[],[f401,f131])).
% 0.22/0.49  fof(f401,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f400,f46])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f399,f35])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f398,f33])).
% 0.22/0.49  fof(f398,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f397,f39])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f396,f37])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f395,f48])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f372,f47])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | v2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(superposition,[],[f59,f36])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f688,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f687,f597])).
% 0.22/0.49  fof(f597,plain,(
% 0.22/0.49    ~v5_pre_topc(sK2,sK0,sK1) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(resolution,[],[f593,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f63,f42])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f41])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f28,f40])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f593,plain,(
% 0.22/0.49    sP5(sK4,sK3,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f592,f172])).
% 0.22/0.49  fof(f592,plain,(
% 0.22/0.49    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | sP5(sK4,sK3,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f591,f236])).
% 0.22/0.49  fof(f591,plain,(
% 0.22/0.49    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | sP5(sK4,sK3,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f590,f204])).
% 0.22/0.49  fof(f590,plain,(
% 0.22/0.49    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | sP5(sK4,sK3,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f585])).
% 0.22/0.49  fof(f585,plain,(
% 0.22/0.49    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | sP5(sK4,sK3,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.49    inference(resolution,[],[f499,f301])).
% 0.22/0.49  fof(f499,plain,(
% 0.22/0.49    ( ! [X2] : (~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2)) | sP5(sK4,X2,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f498,f220])).
% 0.22/0.49  fof(f498,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2)) | sP5(sK4,X2,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f497,f252])).
% 0.22/0.49  fof(f497,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2)) | sP5(sK4,X2,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f489,f188])).
% 0.22/0.49  fof(f489,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X2),u1_struct_0(X2),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X2),X2,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X2)) | sP5(sK4,X2,sK2,sK1,sK0) | ~r4_tsep_1(sK0,sK3,sK4)) )),
% 0.22/0.49    inference(resolution,[],[f19,f418])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | sP5(X4,X3,X2,X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f687,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f686,f42])).
% 0.22/0.49  fof(f686,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f685,f41])).
% 0.22/0.49  fof(f685,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f684,f40])).
% 0.22/0.49  fof(f684,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f683,f45])).
% 0.22/0.49  fof(f683,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f682,f44])).
% 0.22/0.49  fof(f682,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f680,f43])).
% 0.22/0.49  fof(f680,plain,(
% 0.22/0.49    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.49    inference(superposition,[],[f678,f131])).
% 0.22/0.49  fof(f678,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f677,f46])).
% 0.22/0.49  fof(f677,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f676,f35])).
% 0.22/0.49  fof(f676,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f675,f33])).
% 0.22/0.49  fof(f675,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f674,f39])).
% 0.22/0.49  fof(f674,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f673,f37])).
% 0.22/0.49  fof(f673,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f672,f48])).
% 0.22/0.49  fof(f672,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f669,f47])).
% 0.22/0.49  fof(f669,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK3,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK3,X1),u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK3,X1),sK3,X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK4,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK4,X1),u1_struct_0(sK4),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK4,X1),sK4,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0)) )),
% 0.22/0.49    inference(superposition,[],[f51,f36])).
% 0.22/0.49  % (13041)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | v2_struct_0(X0) | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (13036)------------------------------
% 0.22/0.49  % (13036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13036)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (13036)Memory used [KB]: 7419
% 0.22/0.49  % (13036)Time elapsed: 0.089 s
% 0.22/0.49  % (13036)------------------------------
% 0.22/0.49  % (13036)------------------------------
% 0.22/0.49  % (13022)Success in time 0.13 s
%------------------------------------------------------------------------------
