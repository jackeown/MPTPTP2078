%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 518 expanded)
%              Number of leaves         :    9 (  92 expanded)
%              Depth                    :   27
%              Number of atoms          :  948 (7725 expanded)
%              Number of equality atoms :   27 ( 317 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f563,plain,(
    $false ),
    inference(subsumption_resolution,[],[f562,f406])).

fof(f406,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f402,f243])).

fof(f243,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f33,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f402,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f169,f192])).

fof(f192,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f42,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f169,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f40,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f562,plain,(
    ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f558,f33])).

fof(f558,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f556,f396])).

fof(f396,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f395,f351])).

fof(f351,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f350,f67])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f30,f34])).

fof(f34,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f350,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f349,f35])).

fof(f35,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f349,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f348,f40])).

fof(f348,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f347,f39])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f347,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f346,f38])).

fof(f38,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f346,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f345,f37])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f345,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f344,f42])).

fof(f344,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f343,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f343,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f342,f44])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f342,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f341,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f341,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f340,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f339,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f338,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f337,f47])).

fof(f337,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f336,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f336,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f335,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f335,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(resolution,[],[f68,f65])).

fof(f65,plain,(
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
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7) ) ),
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
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

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

fof(f68,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f29,f34])).

fof(f29,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f395,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f394,f67])).

fof(f394,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f393,f35])).

fof(f393,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f392,f40])).

fof(f392,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f391,f39])).

fof(f391,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f390,f38])).

fof(f390,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f389,f37])).

fof(f389,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f388,f42])).

fof(f388,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f387,f41])).

fof(f387,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f386,f44])).

fof(f386,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f385,f43])).

fof(f385,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f384,f50])).

fof(f384,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f383,f49])).

fof(f383,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f382,f48])).

fof(f382,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f381,f47])).

fof(f381,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f380,f46])).

fof(f380,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(subsumption_resolution,[],[f379,f45])).

fof(f379,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6) ) ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(resolution,[],[f69,f66])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f28,f34])).

fof(f28,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f556,plain,(
    m1_connsp_2(sK5,sK3,sK6) ),
    inference(subsumption_resolution,[],[f555,f35])).

fof(f555,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | m1_connsp_2(sK5,sK3,sK6) ),
    inference(resolution,[],[f550,f32])).

fof(f32,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f550,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f549,f406])).

fof(f549,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f548,f192])).

fof(f548,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f547,f195])).

fof(f195,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f194,f47])).

fof(f194,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f182,f46])).

fof(f182,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f42,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f547,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f545,f41])).

fof(f545,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(superposition,[],[f54,f543])).

fof(f543,plain,(
    sK5 = k1_tops_1(sK3,sK5) ),
    inference(resolution,[],[f536,f36])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f536,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | sK5 = k1_tops_1(sK3,sK5) ) ),
    inference(subsumption_resolution,[],[f532,f46])).

fof(f532,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | sK5 = k1_tops_1(sK3,sK5) ) ),
    inference(resolution,[],[f424,f47])).

fof(f424,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sK5 = k1_tops_1(sK3,sK5) ) ),
    inference(subsumption_resolution,[],[f423,f406])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | sK5 = k1_tops_1(sK3,sK5) ) ),
    inference(subsumption_resolution,[],[f421,f192])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | sK5 = k1_tops_1(sK3,sK5) ) ),
    inference(resolution,[],[f407,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f407,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(resolution,[],[f406,f366])).

fof(f366,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK5,sK3) ),
    inference(resolution,[],[f167,f42])).

fof(f167,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK5,X2) ) ),
    inference(subsumption_resolution,[],[f166,f36])).

fof(f166,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK5,X2) ) ),
    inference(subsumption_resolution,[],[f163,f47])).

fof(f163,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK5,X2) ) ),
    inference(resolution,[],[f31,f64])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f31,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (22506)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.44  % (22506)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f563,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f562,f406])).
% 0.21/0.44  fof(f406,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.44    inference(resolution,[],[f402,f243])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.44    inference(resolution,[],[f33,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.21/0.44  fof(f402,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.44    inference(resolution,[],[f169,f192])).
% 0.21/0.44  fof(f192,plain,(
% 0.21/0.44    l1_pre_topc(sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f180,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    l1_pre_topc(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.21/0.44    inference(resolution,[],[f42,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    m1_pre_topc(sK3,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.44    inference(resolution,[],[f40,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    m1_pre_topc(sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f562,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.44    inference(subsumption_resolution,[],[f558,f33])).
% 0.21/0.44  fof(f558,plain,(
% 0.21/0.44    ~r1_tarski(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.44    inference(resolution,[],[f556,f396])).
% 0.21/0.44  fof(f396,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f395,f351])).
% 0.21/0.44  fof(f351,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f350,f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.44    inference(forward_demodulation,[],[f30,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    sK6 = sK7),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f350,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f349,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f349,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f348,f40])).
% 0.21/0.44  fof(f348,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f347,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f347,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f346,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f346,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f345,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    v1_funct_1(sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f344,f42])).
% 0.21/0.44  fof(f344,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f343,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ~v2_struct_0(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f343,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f342,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    m1_pre_topc(sK2,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f342,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f341,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ~v2_struct_0(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f341,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f340,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f340,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f339,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f339,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f338,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f338,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f337,f47])).
% 0.21/0.44  fof(f337,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f336,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    v2_pre_topc(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f336,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f335,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~v2_struct_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f335,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f333])).
% 0.21/0.44  fof(f333,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.44    inference(resolution,[],[f68,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7)) )),
% 0.21/0.44    inference(equality_resolution,[],[f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.44    inference(forward_demodulation,[],[f29,f34])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f395,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f394,f67])).
% 0.21/0.44  fof(f394,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f393,f35])).
% 0.21/0.44  fof(f393,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f392,f40])).
% 0.21/0.44  fof(f392,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f391,f39])).
% 0.21/0.44  fof(f391,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f390,f38])).
% 0.21/0.44  fof(f390,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f389,f37])).
% 0.21/0.44  fof(f389,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f388,f42])).
% 0.21/0.44  fof(f388,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f387,f41])).
% 0.21/0.44  fof(f387,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f386,f44])).
% 0.21/0.44  fof(f386,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f385,f43])).
% 0.21/0.44  fof(f385,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f384,f50])).
% 0.21/0.44  fof(f384,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f383,f49])).
% 0.21/0.44  fof(f383,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f382,f48])).
% 0.21/0.44  fof(f382,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f381,f47])).
% 0.21/0.44  fof(f381,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f380,f46])).
% 0.21/0.44  fof(f380,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f379,f45])).
% 0.21/0.44  fof(f379,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f377])).
% 0.21/0.44  fof(f377,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.44    inference(resolution,[],[f69,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.21/0.44    inference(equality_resolution,[],[f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.44    inference(forward_demodulation,[],[f28,f34])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f556,plain,(
% 0.21/0.45    m1_connsp_2(sK5,sK3,sK6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f555,f35])).
% 0.21/0.45  fof(f555,plain,(
% 0.21/0.45    ~m1_subset_1(sK6,u1_struct_0(sK3)) | m1_connsp_2(sK5,sK3,sK6)),
% 0.21/0.45    inference(resolution,[],[f550,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    r2_hidden(sK6,sK5)),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f550,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f549,f406])).
% 0.21/0.45  fof(f549,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f548,f192])).
% 0.21/0.45  fof(f548,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK5) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f547,f195])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    v2_pre_topc(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f194,f47])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    ~l1_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f182,f46])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_pre_topc(sK3)),
% 0.21/0.45    inference(resolution,[],[f42,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.45  fof(f547,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK5) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f545,f41])).
% 0.21/0.45  fof(f545,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK5) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.45    inference(superposition,[],[f54,f543])).
% 0.21/0.45  fof(f543,plain,(
% 0.21/0.45    sK5 = k1_tops_1(sK3,sK5)),
% 0.21/0.45    inference(resolution,[],[f536,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f536,plain,(
% 0.21/0.45    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | sK5 = k1_tops_1(sK3,sK5)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f532,f46])).
% 0.21/0.45  fof(f532,plain,(
% 0.21/0.45    ( ! [X4] : (~v2_pre_topc(sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | sK5 = k1_tops_1(sK3,sK5)) )),
% 0.21/0.45    inference(resolution,[],[f424,f47])).
% 0.21/0.45  fof(f424,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sK5 = k1_tops_1(sK3,sK5)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f423,f406])).
% 0.21/0.45  fof(f423,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k1_tops_1(sK3,sK5)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f421,f192])).
% 0.21/0.45  fof(f421,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k1_tops_1(sK3,sK5)) )),
% 0.21/0.45    inference(resolution,[],[f407,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.45  fof(f407,plain,(
% 0.21/0.45    v3_pre_topc(sK5,sK3)),
% 0.21/0.45    inference(resolution,[],[f406,f366])).
% 0.21/0.45  fof(f366,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(sK5,sK3)),
% 0.21/0.45    inference(resolution,[],[f167,f42])).
% 0.21/0.45  fof(f167,plain,(
% 0.21/0.45    ( ! [X2] : (~m1_pre_topc(X2,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK5,X2)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f166,f36])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    ( ! [X2] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK5,X2)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f163,f47])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    ( ! [X2] : (~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK5,X2)) )),
% 0.21/0.45    inference(resolution,[],[f31,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.21/0.45    inference(equality_resolution,[],[f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    v3_pre_topc(sK5,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (22506)------------------------------
% 0.21/0.45  % (22506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (22506)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (22506)Memory used [KB]: 1791
% 0.21/0.45  % (22506)Time elapsed: 0.017 s
% 0.21/0.45  % (22506)------------------------------
% 0.21/0.45  % (22506)------------------------------
% 0.21/0.45  % (22492)Success in time 0.084 s
%------------------------------------------------------------------------------
