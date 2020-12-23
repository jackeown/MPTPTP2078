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
% DateTime   : Thu Dec  3 13:19:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 678 expanded)
%              Number of leaves         :    4 ( 114 expanded)
%              Depth                    :   30
%              Number of atoms          : 1388 (13199 expanded)
%              Number of equality atoms :   14 ( 452 expanded)
%              Maximal formula depth    :   30 (  11 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(global_subsumption,[],[f233,f247,f261])).

fof(f261,plain,(
    v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f260,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).

fof(f260,plain,
    ( ~ v2_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f259,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f259,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f258,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f258,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f257,f31])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f257,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f151,f28])).

fof(f28,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f150,f18])).

fof(f18,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f150,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f149,f15])).

fof(f15,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f149,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f146,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f146,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) ) ),
    inference(resolution,[],[f116,f16])).

fof(f16,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f115,f25])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f114,f22])).

fof(f22,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f111,f33])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f108,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2)) ) ),
    inference(resolution,[],[f23,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f23,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f247,plain,(
    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f246,f135])).

fof(f135,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f133,f28])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | r4_tsep_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | r4_tsep_1(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | r4_tsep_1(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | r4_tsep_1(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | r4_tsep_1(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f53,f36])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | r4_tsep_1(sK0,sK2,X0) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_borsuk_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r4_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f30,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f246,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f245,f47])).

fof(f47,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(backward_demodulation,[],[f21,f19])).

fof(f19,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f245,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f244,f18])).

fof(f244,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f243,f17])).

fof(f17,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f243,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f242,f16])).

fof(f242,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f241,f15])).

fof(f241,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f240,f25])).

fof(f240,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f239,f24])).

fof(f24,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f239,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f238,f23])).

fof(f238,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f237,f22])).

fof(f237,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f236,f34])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f235,f33])).

fof(f235,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f234,f32])).

fof(f234,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f107,f46])).

fof(f46,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(backward_demodulation,[],[f20,f19])).

fof(f20,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f106,f35])).

fof(f106,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f105,f28])).

fof(f105,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f104,f26])).

fof(f104,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f103,f31])).

fof(f103,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f102,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | sK0 != sK0
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9))
      | ~ v5_pre_topc(X10,sK2,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9))
      | ~ v5_pre_topc(X11,sK3,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) ) ),
    inference(superposition,[],[f41,f19])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | k1_tsep_1(X0,X2,X3) != X0
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r4_tsep_1(X0,X2,X3)
      | m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | k1_tsep_1(X0,X2,X3) != X0
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | k1_tsep_1(X0,X2,X3) != X0
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).

fof(f233,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f232,f231])).

fof(f231,plain,(
    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f230,f135])).

fof(f230,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f229,f47])).

fof(f229,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f228,f18])).

fof(f228,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f227,f17])).

fof(f227,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f226,f16])).

fof(f226,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f225,f15])).

fof(f225,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f224,f25])).

fof(f224,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f223,f24])).

fof(f223,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f222,f23])).

fof(f222,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f221,f22])).

fof(f221,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f220,f34])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f219,f33])).

fof(f219,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f218,f32])).

fof(f218,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f93,f46])).

fof(f93,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f90,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f89,f31])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f87,f37])).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | sK0 != sK0
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(X4,sK2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v5_pre_topc(X5,sK3,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3)) ) ),
    inference(superposition,[],[f39,f19])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | k1_tsep_1(X0,X2,X3) != X0
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f232,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f217,f14])).

fof(f14,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f217,plain,(
    v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f216,f135])).

fof(f216,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f215,f47])).

fof(f215,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f214,f18])).

fof(f214,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f213,f17])).

fof(f213,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f212,f16])).

fof(f212,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f211,f15])).

fof(f211,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f210,f25])).

fof(f210,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f209,f24])).

fof(f209,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f208,f23])).

fof(f208,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f207,f22])).

fof(f207,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f206,f34])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f205,f33])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(subsumption_resolution,[],[f204,f32])).

fof(f204,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    inference(resolution,[],[f100,f46])).

fof(f100,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f99,f35])).

fof(f99,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f98,f28])).

fof(f98,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f97,f26])).

fof(f97,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f96,f31])).

fof(f96,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f95,f29])).

fof(f95,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | sK0 != sK0
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v5_pre_topc(X7,sK2,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6))
      | ~ v5_pre_topc(X8,sK3,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
      | v2_struct_0(sK0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6) ) ),
    inference(superposition,[],[f40,f19])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | k1_tsep_1(X0,X2,X3) != X0
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:25:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (25062)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.47  % (25046)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.47  % (25049)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.48  % (25042)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % (25062)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f233,f247,f261])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.48    inference(subsumption_resolution,[],[f259,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.48    inference(subsumption_resolution,[],[f258,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.48    inference(subsumption_resolution,[],[f257,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.48    inference(resolution,[],[f151,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v1_funct_1(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_1(sK5) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_1(sK5) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))) )),
% 0.21/0.48    inference(resolution,[],[f116,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | v1_funct_1(k10_tmap_1(X0,sK1,sK2,X1,sK4,X2))) )),
% 0.21/0.48    inference(resolution,[],[f23,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f246,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    r4_tsep_1(sK0,sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f28])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK0) | r4_tsep_1(sK0,sK2,sK3)),
% 0.21/0.48    inference(resolution,[],[f57,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_borsuk_1(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | r4_tsep_1(sK0,sK2,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f31])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | r4_tsep_1(sK0,sK2,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f35])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | r4_tsep_1(sK0,sK2,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f37])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | r4_tsep_1(sK0,sK2,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f36])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | r4_tsep_1(sK0,sK2,X0)) )),
% 0.21/0.48    inference(resolution,[],[f30,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_borsuk_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X2,X0) | r4_tsep_1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_borsuk_1(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.21/0.48    inference(backward_demodulation,[],[f21,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f244,f18])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v5_pre_topc(sK5,sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f242,f16])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f241,f15])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f25])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f239,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v5_pre_topc(sK4,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f238,f23])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f237,f22])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f236,f34])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f235,f33])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f32])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(resolution,[],[f107,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.21/0.48    inference(backward_demodulation,[],[f20,f19])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f35])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f28])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f26])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f31])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f29])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f37])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f36])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X10,X11,X9] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK2,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | sK0 != sK0 | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(sK2),u1_struct_0(X9)) | ~v5_pre_topc(X10,sK2,X9) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X9)))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X9)) | ~v5_pre_topc(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X9)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X9),k3_tmap_1(sK0,X9,sK0,sK3,k10_tmap_1(sK0,X9,sK2,sK3,X10,X11)),X11) | ~r4_tsep_1(sK0,sK2,sK3) | m1_subset_1(k10_tmap_1(sK0,X9,sK2,sK3,X10,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))) )),
% 0.21/0.49    inference(superposition,[],[f41,f19])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | k1_tsep_1(X0,X2,X3) != X0 | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r4_tsep_1(X0,X2,X3) | m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | k1_tsep_1(X0,X2,X3) != X0 | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | k1_tsep_1(X0,X2,X3) != X0) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f135])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f229,f47])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f18])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f227,f17])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f16])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f225,f15])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f25])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f24])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f23])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f22])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f34])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f219,f33])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f32])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f93,f46])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f35])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f28])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f26])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f31])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f29])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f37])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f36])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK2,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | sK0 != sK0 | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X4,sK2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X3)) | ~v5_pre_topc(X5,sK3,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X3),k3_tmap_1(sK0,X3,sK0,sK3,k10_tmap_1(sK0,X3,sK2,sK3,X4,X5)),X5) | ~r4_tsep_1(sK0,sK2,sK3) | v1_funct_2(k10_tmap_1(sK0,X3,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(X3))) )),
% 0.21/0.49    inference(superposition,[],[f39,f19])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | k1_tsep_1(X0,X2,X3) != X0 | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r4_tsep_1(X0,X2,X3) | v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(resolution,[],[f217,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f135])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f47])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f18])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f213,f17])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f16])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f15])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f210,f25])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f209,f24])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f208,f23])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f207,f22])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f34])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f205,f33])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f204,f32])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f100,f46])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f35])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f28])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f26])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f31])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f29])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f37])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | ~l1_pre_topc(sK0) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f36])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK2,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X7) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | sK0 != sK0 | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(X6)) | ~v5_pre_topc(X7,sK2,X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X6)) | ~v5_pre_topc(X8,sK3,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | v2_struct_0(sK0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X6),k3_tmap_1(sK0,X6,sK0,sK3,k10_tmap_1(sK0,X6,sK2,sK3,X7,X8)),X8) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X6,sK2,sK3,X7,X8),sK0,X6)) )),
% 0.21/0.49    inference(superposition,[],[f40,f19])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | k1_tsep_1(X0,X2,X3) != X0 | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (25062)------------------------------
% 0.21/0.49  % (25062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25062)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (25062)Memory used [KB]: 6524
% 0.21/0.49  % (25062)Time elapsed: 0.076 s
% 0.21/0.49  % (25062)------------------------------
% 0.21/0.49  % (25062)------------------------------
% 0.21/0.49  % (25035)Success in time 0.124 s
%------------------------------------------------------------------------------
