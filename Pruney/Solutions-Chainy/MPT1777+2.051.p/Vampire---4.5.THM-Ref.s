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
% DateTime   : Thu Dec  3 13:19:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 605 expanded)
%              Number of leaves         :   12 ( 112 expanded)
%              Depth                    :   23
%              Number of atoms          :  587 (6660 expanded)
%              Number of equality atoms :   18 ( 613 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(global_subsumption,[],[f155,f169,f318])).

fof(f318,plain,(
    sP9(sK3,sK2,sK5) ),
    inference(resolution,[],[f213,f301])).

fof(f301,plain,(
    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) ),
    inference(resolution,[],[f255,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f255,plain,(
    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f211,f240])).

fof(f240,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f239,f179])).

fof(f179,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f175,f83])).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f175,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f169,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f239,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(resolution,[],[f234,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f234,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f230,f96])).

fof(f96,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f91,f49])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f64])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f225,f61])).

fof(f225,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f223,f83])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f122,f104])).

fof(f104,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f121,f96])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK2) ) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f211,plain,(
    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f210,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f210,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f209,f35])).

fof(f35,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f209,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f208,f83])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f205,f85])).

fof(f85,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f84,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f79,f49])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f205,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f108,plain,(
    m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,
    ( v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f106,f83])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(resolution,[],[f35,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f213,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(X1))
      | sP9(sK3,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f207,f211])).

fof(f207,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(X1))
      | ~ m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
      | sP9(sK3,X1,sK5) ) ),
    inference(resolution,[],[f108,f72])).

fof(f72,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | sP9(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_connsp_2(X5,X3,X7)
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
    <=> ~ sP9(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f169,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f168,f39])).

fof(f168,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f167,f96])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f96,f65])).

fof(f155,plain,
    ( ~ sP9(sK3,sK2,sK5)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f154,f34])).

fof(f34,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f153,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f153,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f152,f75])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f31,f32])).

fof(f32,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f151,f35])).

fof(f151,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f150,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f150,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f149,f37])).

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f149,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f148,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f146,f40])).

fof(f146,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f145,f43])).

fof(f145,plain,
    ( ~ m1_pre_topc(sK2,sK0)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f144,plain,
    ( v2_struct_0(sK2)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f143,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK1)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f142,plain,
    ( ~ v2_pre_topc(sK1)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,
    ( v2_struct_0(sK1)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f140,f49])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
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
    | ~ sP9(sK3,sK2,sK5) ),
    inference(resolution,[],[f74,f73])).

fof(f73,plain,(
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
      | ~ sP9(X3,X2,X7) ) ),
    inference(general_splitting,[],[f67,f72_D])).

fof(f67,plain,(
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
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f74,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f33,f32])).

fof(f33,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16321)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16321)Refutation not found, incomplete strategy% (16321)------------------------------
% 0.21/0.51  % (16321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16326)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (16322)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16340)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (16334)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16323)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (16339)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (16326)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (16325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (16342)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (16338)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (16346)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f155,f169,f318])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(resolution,[],[f213,f301])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f255,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    inference(backward_demodulation,[],[f211,f240])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f239,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f175,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    l1_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f41,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    inference(resolution,[],[f169,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f234,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f230,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f49])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f43,f64])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    ~l1_pre_topc(sK2) | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f225,f61])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f83])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | m1_pre_topc(sK3,sK2)),
% 0.21/0.52    inference(resolution,[],[f122,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK3)),
% 0.21/0.52    inference(resolution,[],[f83,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f96])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f55,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f210,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ~v2_struct_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f83])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    v2_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f49])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f41,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(resolution,[],[f108,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f40])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f83])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f85])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.52    inference(resolution,[],[f35,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK7(X0,X1),X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(sK7(sK3,sK5),u1_struct_0(X1)) | sP9(sK3,X1,sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f211])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(sK7(sK3,sK5),u1_struct_0(X1)) | ~m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | sP9(sK3,X1,sK5)) )),
% 0.21/0.52    inference(resolution,[],[f108,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X7,X5,X3] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | sP9(X3,X2,X7)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f72_D])).
% 0.21/0.52  fof(f72_D,plain,(
% 0.21/0.52    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) ) <=> ~sP9(X3,X2,X7)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK3)),
% 0.21/0.52    inference(forward_demodulation,[],[f168,f39])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f96])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f113,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK2)),
% 0.21/0.52    inference(resolution,[],[f96,f65])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~sP9(sK3,sK2,sK5) | ~m1_pre_topc(sK2,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f154,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f31,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    sK5 = sK6),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f35])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f148,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f41])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f40])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f43])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f144,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ~v2_struct_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f143,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f140,f49])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f138,f48])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 0.21/0.52    inference(resolution,[],[f74,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7) | ~sP9(X3,X2,X7)) )),
% 0.21/0.52    inference(general_splitting,[],[f67,f72_D])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.52    inference(backward_demodulation,[],[f33,f32])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16326)------------------------------
% 0.21/0.52  % (16326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16326)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16326)Memory used [KB]: 6396
% 0.21/0.52  % (16326)Time elapsed: 0.093 s
% 0.21/0.52  % (16326)------------------------------
% 0.21/0.52  % (16326)------------------------------
% 0.21/0.52  % (16332)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (16324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (16320)Success in time 0.155 s
%------------------------------------------------------------------------------
