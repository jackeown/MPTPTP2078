%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 529 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  607 (5955 expanded)
%              Number of equality atoms :   35 ( 566 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(global_subsumption,[],[f174,f207,f417])).

fof(f417,plain,(
    sP9(sK3,sK2,sK5) ),
    inference(resolution,[],[f255,f378])).

fof(f378,plain,(
    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f321,f368])).

fof(f368,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(trivial_inequality_removal,[],[f367])).

fof(f367,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(superposition,[],[f293,f46])).

fof(f46,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f293,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK3
      | u1_struct_0(sK3) = X0 ) ),
    inference(forward_demodulation,[],[f290,f131])).

fof(f131,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f130,f94])).

fof(f94,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f88,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f48,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK3)
    | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f108,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f108,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f107,f46])).

fof(f107,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f50,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f290,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | u1_struct_0(sK3) = X0 ) ),
    inference(resolution,[],[f119,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f119,plain,(
    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f321,plain,(
    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[],[f253,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f253,plain,(
    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f252,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f252,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f251,f42])).

fof(f42,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f251,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f250,f94])).

fof(f250,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f247,f96])).

fof(f96,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f89,f56])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
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

fof(f247,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f123,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f123,plain,(
    m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f122,f47])).

fof(f122,plain,
    ( v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f121,f94])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(subsumption_resolution,[],[f120,f96])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | m1_connsp_2(sK7(sK3,sK5),sK3,sK5) ),
    inference(resolution,[],[f42,f70])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f255,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(X1))
      | sP9(sK3,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f249,f253])).

fof(f249,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(X1))
      | ~ m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
      | sP9(sK3,X1,sK5) ) ),
    inference(resolution,[],[f123,f78])).

fof(f78,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | sP9(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f78_D])).

fof(f78_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_connsp_2(X5,X3,X7)
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
    <=> ~ sP9(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f207,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f206,f46])).

fof(f206,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f201,f111])).

fof(f111,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f103,f56])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f50,f68])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f128,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f128,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f111,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f174,plain,
    ( ~ sP9(sK3,sK2,sK5)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f173,f41])).

% (18966)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (18956)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (18957)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (18967)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (18969)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (18960)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (18975)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (18974)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (18977)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (18976)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (18963)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (18978)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (18962)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (18970)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (18963)Refutation not found, incomplete strategy% (18963)------------------------------
% (18963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f41,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f173,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f172,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f171,f81])).

fof(f81,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f170,f42])).

fof(f170,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f169,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f169,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f168,f44])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f168,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f167,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f167,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ sP9(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f166,f48])).

fof(f166,plain,
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
    inference(subsumption_resolution,[],[f165,f47])).

fof(f165,plain,
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
    inference(subsumption_resolution,[],[f164,f50])).

fof(f164,plain,
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
    inference(subsumption_resolution,[],[f163,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f163,plain,
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
    inference(subsumption_resolution,[],[f162,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f162,plain,
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
    inference(subsumption_resolution,[],[f161,f52])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f161,plain,
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
    inference(subsumption_resolution,[],[f160,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f160,plain,
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
    inference(subsumption_resolution,[],[f159,f56])).

fof(f159,plain,
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
    inference(subsumption_resolution,[],[f157,f55])).

fof(f157,plain,
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
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
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
    inference(general_splitting,[],[f75,f78_D])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f80,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f40,f39])).

fof(f40,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (18965)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (18973)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (18958)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (18961)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (18959)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (18981)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (18961)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f174,f207,f417])).
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    sP9(sK3,sK2,sK5)),
% 0.21/0.49    inference(resolution,[],[f255,f378])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f321,f368])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f367])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.49    inference(superposition,[],[f293,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK3) = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f290,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    l1_pre_topc(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f48,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.49    inference(resolution,[],[f108,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    v1_pre_topc(sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f107,f46])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f56])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.49    inference(resolution,[],[f50,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | u1_struct_0(sK3) = X0) )),
% 0.21/0.49    inference(resolution,[],[f119,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.49    inference(resolution,[],[f94,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    r1_tarski(sK7(sK3,sK5),u1_struct_0(sK3))),
% 0.21/0.49    inference(resolution,[],[f253,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~v2_struct_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f251,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f250,f94])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f247,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v2_pre_topc(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f56])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f48,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    inference(resolution,[],[f123,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f47])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f121,f94])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f96])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | m1_connsp_2(sK7(sK3,sK5),sK3,sK5)),
% 0.21/0.50    inference(resolution,[],[f42,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK7(X0,X1),X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK7(sK3,sK5),u1_struct_0(X1)) | sP9(sK3,X1,sK5)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f253])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK7(sK3,sK5),u1_struct_0(X1)) | ~m1_subset_1(sK7(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | sP9(sK3,X1,sK5)) )),
% 0.21/0.50    inference(resolution,[],[f123,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X7,X5,X3] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | sP9(X3,X2,X7)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f78_D])).
% 0.21/0.50  fof(f78_D,plain,(
% 0.21/0.50    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) ) <=> ~sP9(X3,X2,X7)) )),
% 0.21/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f206,f46])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f201,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f103,f56])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.50    inference(resolution,[],[f50,f68])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 0.21/0.50    inference(resolution,[],[f128,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK2)),
% 0.21/0.50    inference(resolution,[],[f111,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~sP9(sK3,sK2,sK5) | ~m1_pre_topc(sK2,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f173,f41])).
% 0.21/0.50  % (18966)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (18956)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (18957)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (18967)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (18969)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (18960)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (18975)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (18974)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (18977)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (18976)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (18963)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.23/0.52  % (18978)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.23/0.52  % (18962)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.23/0.52  % (18970)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.52  % (18963)Refutation not found, incomplete strategy% (18963)------------------------------
% 1.23/0.52  % (18963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f173,plain,(
% 1.23/0.52    ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f172,f54])).
% 1.23/0.52  fof(f54,plain,(
% 1.23/0.52    ~v2_struct_0(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f172,plain,(
% 1.23/0.52    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f171,f81])).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.23/0.52    inference(forward_demodulation,[],[f38,f39])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    sK5 = sK6),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f171,plain,(
% 1.23/0.52    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f170,f42])).
% 1.23/0.52  fof(f170,plain,(
% 1.23/0.52    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f169,f45])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f169,plain,(
% 1.23/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f168,f44])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f168,plain,(
% 1.23/0.52    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f167,f43])).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    v1_funct_1(sK4)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f167,plain,(
% 1.23/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f166,f48])).
% 1.23/0.52  fof(f166,plain,(
% 1.23/0.52    ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f165,f47])).
% 1.23/0.52  fof(f165,plain,(
% 1.23/0.52    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f164,f50])).
% 1.23/0.52  fof(f164,plain,(
% 1.23/0.52    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f163,f49])).
% 1.23/0.52  fof(f49,plain,(
% 1.23/0.52    ~v2_struct_0(sK2)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f163,plain,(
% 1.23/0.52    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f162,f53])).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    l1_pre_topc(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f162,plain,(
% 1.23/0.52    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f161,f52])).
% 1.23/0.52  fof(f52,plain,(
% 1.23/0.52    v2_pre_topc(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f161,plain,(
% 1.23/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f160,f51])).
% 1.23/0.52  fof(f51,plain,(
% 1.23/0.52    ~v2_struct_0(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f160,plain,(
% 1.23/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f159,f56])).
% 1.23/0.52  fof(f159,plain,(
% 1.23/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f157,f55])).
% 1.23/0.52  fof(f157,plain,(
% 1.23/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~sP9(sK3,sK2,sK5)),
% 1.23/0.52    inference(resolution,[],[f80,f79])).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7) | ~sP9(X3,X2,X7)) )),
% 1.23/0.52    inference(general_splitting,[],[f75,f78_D])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 1.23/0.52    inference(equality_resolution,[],[f57])).
% 1.23/0.52  fof(f57,plain,(
% 1.23/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.23/0.52    inference(flattening,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,axiom,(
% 1.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 1.23/0.52  fof(f80,plain,(
% 1.23/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.23/0.52    inference(backward_demodulation,[],[f40,f39])).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (18961)------------------------------
% 1.23/0.52  % (18961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (18961)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (18961)Memory used [KB]: 6396
% 1.23/0.52  % (18961)Time elapsed: 0.093 s
% 1.23/0.52  % (18961)------------------------------
% 1.23/0.52  % (18961)------------------------------
% 1.23/0.52  % (18968)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.23/0.52  % (18972)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.23/0.52  % (18955)Success in time 0.166 s
%------------------------------------------------------------------------------
