%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:56 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  185 (3787 expanded)
%              Number of leaves         :   16 ( 676 expanded)
%              Depth                    :   44
%              Number of atoms          : 1151 (44942 expanded)
%              Number of equality atoms :   23 (2046 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1306,plain,(
    $false ),
    inference(global_subsumption,[],[f98,f511,f1305])).

fof(f1305,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f1304,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f1304,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f1303,f97])).

fof(f97,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f42,f43])).

fof(f43,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f1303,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(resolution,[],[f1048,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f1048,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f1047,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1047,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f1046,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1046,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f1045,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1045,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK0)
      | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5) ) ),
    inference(resolution,[],[f565,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f564,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f564,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f563,f44])).

fof(f44,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f563,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f562,f47])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f562,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f561,f46])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f561,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f560,f45])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f560,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f559,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f559,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f558,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f558,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f557,f55])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f557,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f555,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f555,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(resolution,[],[f511,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,X4,X6)
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f511,plain,(
    r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f500,f162])).

fof(f162,plain,
    ( ~ sP10(sK3,sK2,sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f161,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f160,f97])).

fof(f160,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f159,f44])).

fof(f159,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f158,f49])).

fof(f158,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f157,f47])).

fof(f157,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f156,f46])).

fof(f156,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f155,f45])).

fof(f155,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f154,f51])).

fof(f154,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f153,f50])).

fof(f153,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f152,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f151,f52])).

fof(f151,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f150,f56])).

fof(f150,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f149,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f148,f54])).

fof(f148,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f147,f59])).

fof(f147,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f146,f58])).

fof(f146,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP10(sK3,sK2,sK5) ),
    inference(resolution,[],[f99,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
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
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ sP10(X3,X2,X7) ) ),
    inference(general_splitting,[],[f86,f95_D])).

fof(f95,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | sP10(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f95_D])).

fof(f95_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ r2_hidden(X7,X5)
          | ~ v3_pre_topc(X5,X3)
          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r1_tarski(X5,u1_struct_0(X2)) )
    <=> ~ sP10(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f86,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X7,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X6,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f99,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(forward_demodulation,[],[f40,f43])).

fof(f40,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f500,plain,(
    sP10(sK3,sK2,sK5) ),
    inference(resolution,[],[f363,f319])).

fof(f319,plain,(
    r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f311,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f311,plain,(
    m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f214,f230])).

fof(f230,plain,(
    m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f229,f52])).

fof(f229,plain,
    ( v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f228,f97])).

fof(f228,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f227,f124])).

fof(f124,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f119,f59])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f53,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f227,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f210,f126])).

fof(f126,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f125,f58])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f120,f59])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f210,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f138,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f138,plain,(
    m1_connsp_2(sK7(sK2,sK5),sK2,sK5) ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,
    ( v2_struct_0(sK2)
    | m1_connsp_2(sK7(sK2,sK5),sK2,sK5) ),
    inference(subsumption_resolution,[],[f136,f124])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | m1_connsp_2(sK7(sK2,sK5),sK2,sK5) ),
    inference(subsumption_resolution,[],[f135,f126])).

fof(f135,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | m1_connsp_2(sK7(sK2,sK5),sK2,sK5) ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f214,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f213,f52])).

fof(f213,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f212,f97])).

fof(f212,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f211,f124])).

fof(f211,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f206,f126])).

fof(f206,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f363,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X0))
      | sP10(sK3,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f361,f320])).

fof(f320,plain,(
    m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f317,f112])).

fof(f112,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f107,f59])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f51,f76])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f311,f106])).

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK3)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f49,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f361,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X0))
      | sP10(sK3,X0,sK5) ) ),
    inference(resolution,[],[f307,f337])).

fof(f337,plain,(
    v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) ),
    inference(resolution,[],[f297,f320])).

fof(f297,plain,
    ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) ),
    inference(global_subsumption,[],[f214,f230,f296])).

fof(f296,plain,
    ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) ),
    inference(subsumption_resolution,[],[f295,f73])).

fof(f295,plain,
    ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) ),
    inference(subsumption_resolution,[],[f294,f49])).

fof(f294,plain,
    ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f291,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f291,plain,
    ( ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f286,f242])).

fof(f242,plain,(
    ! [X2,X3] :
      ( ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(sK2))
      | v3_pre_topc(X3,sK3)
      | ~ m1_pre_topc(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f241,f114])).

fof(f114,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f108,f59])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f51,f75])).

fof(f241,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_pre_topc(sK3)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(sK2))
      | v3_pre_topc(X3,sK3)
      | ~ v3_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f240,f174])).

fof(f174,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f105,f112])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f49,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f240,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_pre_topc(sK3)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(sK2))
      | v3_pre_topc(X3,sK3)
      | ~ v3_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f236,f112])).

fof(f236,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_pre_topc(sK3)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(sK2))
      | v3_pre_topc(X3,sK3)
      | ~ v3_pre_topc(X3,X2) ) ),
    inference(resolution,[],[f233,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tarski(X4,X2)
      | v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tarski(X3,X2)
      | X3 != X4
      | v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( X3 = X4
                          & r1_tarski(X3,X2)
                          & r1_tarski(X2,u1_struct_0(X1))
                          & v3_pre_topc(X2,X0) )
                       => ( v3_pre_topc(X4,X1)
                        <=> v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

fof(f233,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f232,f114])).

fof(f232,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f231,f112])).

fof(f231,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f101,f174])).

fof(f101,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f48,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f48,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f286,plain,(
    v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) ),
    inference(resolution,[],[f218,f230])).

fof(f218,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) ),
    inference(subsumption_resolution,[],[f217,f52])).

fof(f217,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f216,f97])).

fof(f216,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f215,f124])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f207,f126])).

fof(f207,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f138,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK8(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f307,plain,(
    ! [X4,X5] :
      ( ~ v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),X4)
      | ~ m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X5))
      | sP10(X4,X5,sK5) ) ),
    inference(resolution,[],[f290,f95])).

fof(f290,plain,(
    r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) ),
    inference(resolution,[],[f226,f230])).

fof(f226,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) ),
    inference(subsumption_resolution,[],[f225,f52])).

fof(f225,plain,
    ( ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f224,f97])).

fof(f224,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f223,f124])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f209,f126])).

fof(f209,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f138,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,sK8(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(forward_demodulation,[],[f41,f43])).

fof(f41,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:48:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.50  % (5067)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (5086)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (5070)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (5074)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (5068)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (5069)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (5083)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (5089)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (5078)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (5081)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (5065)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (5079)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (5066)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (5087)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (5084)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.55  % (5085)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (5076)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.55  % (5088)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  % (5071)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.56  % (5082)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (5080)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.56  % (5090)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (5073)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.56  % (5077)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.56  % (5065)Refutation not found, incomplete strategy% (5065)------------------------------
% 0.20/0.56  % (5065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5065)Memory used [KB]: 10746
% 0.20/0.56  % (5065)Time elapsed: 0.128 s
% 0.20/0.56  % (5065)------------------------------
% 0.20/0.56  % (5065)------------------------------
% 1.64/0.56  % (5075)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.64/0.57  % (5066)Refutation not found, incomplete strategy% (5066)------------------------------
% 1.64/0.57  % (5066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (5066)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (5066)Memory used [KB]: 10874
% 1.64/0.57  % (5066)Time elapsed: 0.159 s
% 1.64/0.57  % (5066)------------------------------
% 1.64/0.57  % (5066)------------------------------
% 1.64/0.57  % (5072)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.83/0.59  % (5071)Refutation not found, incomplete strategy% (5071)------------------------------
% 1.83/0.59  % (5071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.59  % (5071)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.59  
% 1.83/0.59  % (5071)Memory used [KB]: 10874
% 1.83/0.59  % (5071)Time elapsed: 0.106 s
% 1.83/0.59  % (5071)------------------------------
% 1.83/0.59  % (5071)------------------------------
% 1.83/0.59  % (5070)Refutation found. Thanks to Tanya!
% 1.83/0.59  % SZS status Theorem for theBenchmark
% 1.83/0.59  % SZS output start Proof for theBenchmark
% 1.83/0.59  fof(f1306,plain,(
% 1.83/0.59    $false),
% 1.83/0.59    inference(global_subsumption,[],[f98,f511,f1305])).
% 1.83/0.59  fof(f1305,plain,(
% 1.83/0.59    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.83/0.59    inference(subsumption_resolution,[],[f1304,f52])).
% 1.83/0.59  fof(f52,plain,(
% 1.83/0.59    ~v2_struct_0(sK2)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f18,plain,(
% 1.83/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.83/0.59    inference(flattening,[],[f17])).
% 1.83/0.59  fof(f17,plain,(
% 1.83/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.83/0.59    inference(ennf_transformation,[],[f16])).
% 1.83/0.59  fof(f16,negated_conjecture,(
% 1.83/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.83/0.59    inference(negated_conjecture,[],[f15])).
% 1.83/0.59  fof(f15,conjecture,(
% 1.83/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.83/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.83/0.59  fof(f1304,plain,(
% 1.83/0.59    v2_struct_0(sK2) | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.83/0.59    inference(subsumption_resolution,[],[f1303,f97])).
% 1.83/0.59  fof(f97,plain,(
% 1.83/0.59    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.83/0.59    inference(forward_demodulation,[],[f42,f43])).
% 1.83/0.59  fof(f43,plain,(
% 1.83/0.59    sK5 = sK6),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f42,plain,(
% 1.83/0.59    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f1303,plain,(
% 1.83/0.59    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.83/0.59    inference(resolution,[],[f1048,f49])).
% 1.83/0.59  fof(f49,plain,(
% 1.83/0.59    m1_pre_topc(sK2,sK3)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f1048,plain,(
% 1.83/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f1047,f57])).
% 1.83/0.59  fof(f57,plain,(
% 1.83/0.59    ~v2_struct_0(sK0)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f1047,plain,(
% 1.83/0.59    ( ! [X0] : (v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f1046,f58])).
% 1.83/0.59  fof(f58,plain,(
% 1.83/0.59    v2_pre_topc(sK0)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f1046,plain,(
% 1.83/0.59    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f1045,f59])).
% 1.83/0.59  fof(f59,plain,(
% 1.83/0.59    l1_pre_topc(sK0)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f1045,plain,(
% 1.83/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK5)) )),
% 1.83/0.59    inference(resolution,[],[f565,f51])).
% 1.83/0.59  fof(f51,plain,(
% 1.83/0.59    m1_pre_topc(sK3,sK0)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f565,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X1) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f564,f74])).
% 1.83/0.59  fof(f74,plain,(
% 1.83/0.59    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.83/0.59    inference(cnf_transformation,[],[f30])).
% 1.83/0.59  fof(f30,plain,(
% 1.83/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.83/0.59    inference(flattening,[],[f29])).
% 1.83/0.59  fof(f29,plain,(
% 1.83/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.83/0.59    inference(ennf_transformation,[],[f11])).
% 1.83/0.59  fof(f11,axiom,(
% 1.83/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.83/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.83/0.59  fof(f564,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f563,f44])).
% 1.83/0.59  fof(f44,plain,(
% 1.83/0.59    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f563,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f562,f47])).
% 1.83/0.59  fof(f47,plain,(
% 1.83/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f562,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f561,f46])).
% 1.83/0.59  fof(f46,plain,(
% 1.83/0.59    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f561,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f560,f45])).
% 1.83/0.59  fof(f45,plain,(
% 1.83/0.59    v1_funct_1(sK4)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f560,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f559,f50])).
% 1.83/0.59  fof(f50,plain,(
% 1.83/0.59    ~v2_struct_0(sK3)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f559,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f558,f56])).
% 1.83/0.59  fof(f56,plain,(
% 1.83/0.59    l1_pre_topc(sK1)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f558,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f557,f55])).
% 1.83/0.59  fof(f55,plain,(
% 1.83/0.59    v2_pre_topc(sK1)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f557,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(subsumption_resolution,[],[f555,f54])).
% 1.83/0.59  fof(f54,plain,(
% 1.83/0.59    ~v2_struct_0(sK1)),
% 1.83/0.59    inference(cnf_transformation,[],[f18])).
% 1.83/0.59  fof(f555,plain,(
% 1.83/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 1.83/0.59    inference(resolution,[],[f511,f84])).
% 1.83/0.60  fof(f84,plain,(
% 1.83/0.60    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,X4,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X0) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 1.83/0.60    inference(equality_resolution,[],[f60])).
% 1.83/0.60  fof(f60,plain,(
% 1.83/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f20])).
% 1.83/0.60  fof(f20,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.60    inference(flattening,[],[f19])).
% 1.83/0.60  fof(f19,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f12])).
% 1.83/0.60  fof(f12,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.83/0.60  fof(f511,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(resolution,[],[f500,f162])).
% 1.83/0.60  fof(f162,plain,(
% 1.83/0.60    ~sP10(sK3,sK2,sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f161,f57])).
% 1.83/0.60  fof(f161,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f160,f97])).
% 1.83/0.60  fof(f160,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f159,f44])).
% 1.83/0.60  fof(f159,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f158,f49])).
% 1.83/0.60  fof(f158,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f157,f47])).
% 1.83/0.60  fof(f157,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f156,f46])).
% 1.83/0.60  fof(f156,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f155,f45])).
% 1.83/0.60  fof(f155,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f154,f51])).
% 1.83/0.60  fof(f154,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f153,f50])).
% 1.83/0.60  fof(f153,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f152,f53])).
% 1.83/0.60  fof(f53,plain,(
% 1.83/0.60    m1_pre_topc(sK2,sK0)),
% 1.83/0.60    inference(cnf_transformation,[],[f18])).
% 1.83/0.60  fof(f152,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f151,f52])).
% 1.83/0.60  fof(f151,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f150,f56])).
% 1.83/0.60  fof(f150,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f149,f55])).
% 1.83/0.60  fof(f149,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f148,f54])).
% 1.83/0.60  fof(f148,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f147,f59])).
% 1.83/0.60  fof(f147,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f146,f58])).
% 1.83/0.60  fof(f146,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(duplicate_literal_removal,[],[f143])).
% 1.83/0.60  fof(f143,plain,(
% 1.83/0.60    r1_tmap_1(sK3,sK1,sK4,sK5) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(resolution,[],[f99,f96])).
% 1.83/0.60  fof(f96,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7) | ~sP10(X3,X2,X7)) )),
% 1.83/0.60    inference(general_splitting,[],[f86,f95_D])).
% 1.83/0.60  fof(f95,plain,(
% 1.83/0.60    ( ! [X2,X7,X5,X3] : (~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | sP10(X3,X2,X7)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f95_D])).
% 1.83/0.60  fof(f95_D,plain,(
% 1.83/0.60    ( ! [X7,X2,X3] : (( ! [X5] : (~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2))) ) <=> ~sP10(X3,X2,X7)) )),
% 1.83/0.60    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 1.83/0.60  fof(f86,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 1.83/0.60    inference(equality_resolution,[],[f61])).
% 1.83/0.60  fof(f61,plain,(
% 1.83/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X6,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f22])).
% 1.83/0.60  fof(f22,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.60    inference(flattening,[],[f21])).
% 1.83/0.60  fof(f21,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f13])).
% 1.83/0.60  fof(f13,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 1.83/0.60  fof(f99,plain,(
% 1.83/0.60    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(forward_demodulation,[],[f40,f43])).
% 1.83/0.60  fof(f40,plain,(
% 1.83/0.60    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(cnf_transformation,[],[f18])).
% 1.83/0.60  fof(f500,plain,(
% 1.83/0.60    sP10(sK3,sK2,sK5)),
% 1.83/0.60    inference(resolution,[],[f363,f319])).
% 1.83/0.60  fof(f319,plain,(
% 1.83/0.60    r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2))),
% 1.83/0.60    inference(resolution,[],[f311,f73])).
% 1.83/0.60  fof(f73,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f2])).
% 1.83/0.60  fof(f2,axiom,(
% 1.83/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.83/0.60  fof(f311,plain,(
% 1.83/0.60    m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(resolution,[],[f214,f230])).
% 1.83/0.60  fof(f230,plain,(
% 1.83/0.60    m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f229,f52])).
% 1.83/0.60  fof(f229,plain,(
% 1.83/0.60    v2_struct_0(sK2) | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f228,f97])).
% 1.83/0.60  fof(f228,plain,(
% 1.83/0.60    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f227,f124])).
% 1.83/0.60  fof(f124,plain,(
% 1.83/0.60    l1_pre_topc(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f119,f59])).
% 1.83/0.60  fof(f119,plain,(
% 1.83/0.60    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 1.83/0.60    inference(resolution,[],[f53,f76])).
% 1.83/0.60  fof(f76,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f33])).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.83/0.60    inference(ennf_transformation,[],[f4])).
% 1.83/0.60  fof(f4,axiom,(
% 1.83/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.83/0.60  fof(f227,plain,(
% 1.83/0.60    ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f210,f126])).
% 1.83/0.60  fof(f126,plain,(
% 1.83/0.60    v2_pre_topc(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f125,f58])).
% 1.83/0.60  fof(f125,plain,(
% 1.83/0.60    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f120,f59])).
% 1.83/0.60  fof(f120,plain,(
% 1.83/0.60    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.83/0.60    inference(resolution,[],[f53,f75])).
% 1.83/0.60  fof(f75,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f32])).
% 1.83/0.60  fof(f32,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.83/0.60    inference(flattening,[],[f31])).
% 1.83/0.60  fof(f31,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f3])).
% 1.83/0.60  fof(f3,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.83/0.60  fof(f210,plain,(
% 1.83/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(resolution,[],[f138,f78])).
% 1.83/0.60  fof(f78,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f37])).
% 1.83/0.60  fof(f37,plain,(
% 1.83/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.60    inference(flattening,[],[f36])).
% 1.83/0.60  fof(f36,plain,(
% 1.83/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f6])).
% 1.83/0.60  fof(f6,axiom,(
% 1.83/0.60    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.83/0.60  fof(f138,plain,(
% 1.83/0.60    m1_connsp_2(sK7(sK2,sK5),sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f137,f52])).
% 1.83/0.60  fof(f137,plain,(
% 1.83/0.60    v2_struct_0(sK2) | m1_connsp_2(sK7(sK2,sK5),sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f136,f124])).
% 1.83/0.60  fof(f136,plain,(
% 1.83/0.60    ~l1_pre_topc(sK2) | v2_struct_0(sK2) | m1_connsp_2(sK7(sK2,sK5),sK2,sK5)),
% 1.83/0.60    inference(subsumption_resolution,[],[f135,f126])).
% 1.83/0.60  fof(f135,plain,(
% 1.83/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | m1_connsp_2(sK7(sK2,sK5),sK2,sK5)),
% 1.83/0.60    inference(resolution,[],[f97,f77])).
% 1.83/0.60  fof(f77,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK7(X0,X1),X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f35])).
% 1.83/0.60  fof(f35,plain,(
% 1.83/0.60    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.60    inference(flattening,[],[f34])).
% 1.83/0.60  fof(f34,plain,(
% 1.83/0.60    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f7])).
% 1.83/0.60  fof(f7,axiom,(
% 1.83/0.60    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 1.83/0.60  fof(f214,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f213,f52])).
% 1.83/0.60  fof(f213,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f212,f97])).
% 1.83/0.60  fof(f212,plain,(
% 1.83/0.60    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f211,f124])).
% 1.83/0.60  fof(f211,plain,(
% 1.83/0.60    ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f206,f126])).
% 1.83/0.60  fof(f206,plain,(
% 1.83/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(resolution,[],[f138,f79])).
% 1.83/0.60  fof(f79,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f39])).
% 1.83/0.60  fof(f39,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.60    inference(flattening,[],[f38])).
% 1.83/0.60  fof(f38,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f8])).
% 1.83/0.60  fof(f8,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 1.83/0.60  fof(f363,plain,(
% 1.83/0.60    ( ! [X0] : (~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X0)) | sP10(sK3,X0,sK5)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f361,f320])).
% 1.83/0.60  fof(f320,plain,(
% 1.83/0.60    m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f317,f112])).
% 1.83/0.60  fof(f112,plain,(
% 1.83/0.60    l1_pre_topc(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f107,f59])).
% 1.83/0.60  fof(f107,plain,(
% 1.83/0.60    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 1.83/0.60    inference(resolution,[],[f51,f76])).
% 1.83/0.60  fof(f317,plain,(
% 1.83/0.60    ~l1_pre_topc(sK3) | m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.83/0.60    inference(resolution,[],[f311,f106])).
% 1.83/0.60  fof(f106,plain,(
% 1.83/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK3) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 1.83/0.60    inference(resolution,[],[f49,f70])).
% 1.83/0.60  fof(f70,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f27])).
% 1.83/0.60  fof(f27,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.83/0.60    inference(ennf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.83/0.60  fof(f361,plain,(
% 1.83/0.60    ( ! [X0] : (~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X0)) | sP10(sK3,X0,sK5)) )),
% 1.83/0.60    inference(resolution,[],[f307,f337])).
% 1.83/0.60  fof(f337,plain,(
% 1.83/0.60    v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)),
% 1.83/0.60    inference(resolution,[],[f297,f320])).
% 1.83/0.60  fof(f297,plain,(
% 1.83/0.60    ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)),
% 1.83/0.60    inference(global_subsumption,[],[f214,f230,f296])).
% 1.83/0.60  fof(f296,plain,(
% 1.83/0.60    ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f295,f73])).
% 1.83/0.60  fof(f295,plain,(
% 1.83/0.60    ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2)) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f294,f49])).
% 1.83/0.60  fof(f294,plain,(
% 1.83/0.60    ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2)) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f291,f88])).
% 1.83/0.60  fof(f88,plain,(
% 1.83/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.83/0.60    inference(equality_resolution,[],[f63])).
% 1.83/0.60  fof(f63,plain,(
% 1.83/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.83/0.60    inference(cnf_transformation,[],[f1])).
% 1.83/0.60  fof(f1,axiom,(
% 1.83/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.60  fof(f291,plain,(
% 1.83/0.60    ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) | ~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(sK2)) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.83/0.60    inference(resolution,[],[f286,f242])).
% 1.83/0.60  fof(f242,plain,(
% 1.83/0.60    ( ! [X2,X3] : (~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(sK2)) | v3_pre_topc(X3,sK3) | ~m1_pre_topc(X2,sK3)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f241,f114])).
% 1.83/0.60  fof(f114,plain,(
% 1.83/0.60    v2_pre_topc(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f113,f58])).
% 1.83/0.60  fof(f113,plain,(
% 1.83/0.60    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f108,f59])).
% 1.83/0.60  fof(f108,plain,(
% 1.83/0.60    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 1.83/0.60    inference(resolution,[],[f51,f75])).
% 1.83/0.60  fof(f241,plain,(
% 1.83/0.60    ( ! [X2,X3] : (~m1_pre_topc(X2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(sK2)) | v3_pre_topc(X3,sK3) | ~v3_pre_topc(X3,X2)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f240,f174])).
% 1.83/0.60  fof(f174,plain,(
% 1.83/0.60    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.83/0.60    inference(resolution,[],[f105,f112])).
% 1.83/0.60  fof(f105,plain,(
% 1.83/0.60    ~l1_pre_topc(sK3) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.83/0.60    inference(resolution,[],[f49,f71])).
% 1.83/0.60  fof(f71,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f28])).
% 1.83/0.60  fof(f28,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.83/0.60    inference(ennf_transformation,[],[f10])).
% 1.83/0.60  fof(f10,axiom,(
% 1.83/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.83/0.60  fof(f240,plain,(
% 1.83/0.60    ( ! [X2,X3] : (~m1_pre_topc(X2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(sK2)) | v3_pre_topc(X3,sK3) | ~v3_pre_topc(X3,X2)) )),
% 1.83/0.60    inference(subsumption_resolution,[],[f236,f112])).
% 1.83/0.60  fof(f236,plain,(
% 1.83/0.60    ( ! [X2,X3] : (~l1_pre_topc(sK3) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(sK2)) | v3_pre_topc(X3,sK3) | ~v3_pre_topc(X3,X2)) )),
% 1.83/0.60    inference(resolution,[],[f233,f89])).
% 1.83/0.60  fof(f89,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X1] : (~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tarski(X4,X2) | v3_pre_topc(X4,X0) | ~v3_pre_topc(X4,X1)) )),
% 1.83/0.60    inference(equality_resolution,[],[f67])).
% 1.83/0.60  fof(f67,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tarski(X3,X2) | X3 != X4 | v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f24])).
% 1.83/0.60  fof(f24,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.83/0.60    inference(flattening,[],[f23])).
% 1.83/0.60  fof(f23,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | (X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f14])).
% 1.83/0.60  fof(f14,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ((X3 = X4 & r1_tarski(X3,X2) & r1_tarski(X2,u1_struct_0(X1)) & v3_pre_topc(X2,X0)) => (v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0))))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).
% 1.83/0.60  fof(f233,plain,(
% 1.83/0.60    v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f232,f114])).
% 1.83/0.60  fof(f232,plain,(
% 1.83/0.60    v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f231,f112])).
% 1.83/0.60  fof(f231,plain,(
% 1.83/0.60    ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3)),
% 1.83/0.60    inference(resolution,[],[f101,f174])).
% 1.83/0.60  fof(f101,plain,(
% 1.83/0.60    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3)),
% 1.83/0.60    inference(subsumption_resolution,[],[f100,f49])).
% 1.83/0.60  fof(f100,plain,(
% 1.83/0.60    ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.83/0.60    inference(resolution,[],[f48,f92])).
% 1.83/0.60  fof(f92,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 1.83/0.60    inference(equality_resolution,[],[f68])).
% 1.83/0.60  fof(f68,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f26])).
% 1.83/0.60  fof(f26,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.83/0.60    inference(flattening,[],[f25])).
% 1.83/0.60  fof(f25,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f9])).
% 1.83/0.60  fof(f9,axiom,(
% 1.83/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.83/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.83/0.60  fof(f48,plain,(
% 1.83/0.60    v1_tsep_1(sK2,sK3)),
% 1.83/0.60    inference(cnf_transformation,[],[f18])).
% 1.83/0.60  fof(f286,plain,(
% 1.83/0.60    v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)),
% 1.83/0.60    inference(resolution,[],[f218,f230])).
% 1.83/0.60  fof(f218,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f217,f52])).
% 1.83/0.60  fof(f217,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f216,f97])).
% 1.83/0.60  fof(f216,plain,(
% 1.83/0.60    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f215,f124])).
% 1.83/0.60  fof(f215,plain,(
% 1.83/0.60    ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f207,f126])).
% 1.83/0.60  fof(f207,plain,(
% 1.83/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),sK2) | v2_struct_0(sK2)),
% 1.83/0.60    inference(resolution,[],[f138,f80])).
% 1.83/0.60  fof(f80,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK8(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f39])).
% 1.83/0.60  fof(f307,plain,(
% 1.83/0.60    ( ! [X4,X5] : (~v3_pre_topc(sK8(sK2,sK5,sK7(sK2,sK5)),X4) | ~m1_subset_1(sK8(sK2,sK5,sK7(sK2,sK5)),k1_zfmisc_1(u1_struct_0(X4))) | ~r1_tarski(sK8(sK2,sK5,sK7(sK2,sK5)),u1_struct_0(X5)) | sP10(X4,X5,sK5)) )),
% 1.83/0.60    inference(resolution,[],[f290,f95])).
% 1.83/0.60  fof(f290,plain,(
% 1.83/0.60    r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))),
% 1.83/0.60    inference(resolution,[],[f226,f230])).
% 1.83/0.60  fof(f226,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5)))),
% 1.83/0.60    inference(subsumption_resolution,[],[f225,f52])).
% 1.83/0.60  fof(f225,plain,(
% 1.83/0.60    ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f224,f97])).
% 1.83/0.60  fof(f224,plain,(
% 1.83/0.60    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f223,f124])).
% 1.83/0.60  fof(f223,plain,(
% 1.83/0.60    ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(subsumption_resolution,[],[f209,f126])).
% 1.83/0.60  fof(f209,plain,(
% 1.83/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK7(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(sK5,sK8(sK2,sK5,sK7(sK2,sK5))) | v2_struct_0(sK2)),
% 1.83/0.60    inference(resolution,[],[f138,f82])).
% 1.83/0.60  fof(f82,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,sK8(X0,X1,X2)) | v2_struct_0(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f39])).
% 1.83/0.60  fof(f98,plain,(
% 1.83/0.60    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(forward_demodulation,[],[f41,f43])).
% 1.83/0.60  fof(f41,plain,(
% 1.83/0.60    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.83/0.60    inference(cnf_transformation,[],[f18])).
% 1.83/0.60  % SZS output end Proof for theBenchmark
% 1.83/0.60  % (5070)------------------------------
% 1.83/0.60  % (5070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (5070)Termination reason: Refutation
% 1.83/0.60  
% 1.83/0.60  % (5070)Memory used [KB]: 7291
% 1.83/0.60  % (5070)Time elapsed: 0.181 s
% 1.83/0.60  % (5070)------------------------------
% 1.83/0.60  % (5070)------------------------------
% 1.83/0.60  % (5064)Success in time 0.259 s
%------------------------------------------------------------------------------
