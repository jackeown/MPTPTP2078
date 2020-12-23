%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 571 expanded)
%              Number of leaves         :    9 ( 102 expanded)
%              Depth                    :   31
%              Number of atoms          :  645 (7711 expanded)
%              Number of equality atoms :   77 ( 433 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(global_subsumption,[],[f93,f95,f198])).

fof(f198,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(backward_demodulation,[],[f31,f197])).

fof(f197,plain,(
    sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f196,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(f196,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f195,f58])).

fof(f58,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f195,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f194,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f194,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f193,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f193,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f192,f71])).

fof(f71,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f67,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f39,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f192,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f189,f53])).

fof(f189,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f188,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f188,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f187,f66])).

fof(f66,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f62,f45])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f37,f54])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f187,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f184,f53])).

fof(f184,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f183,f176])).

fof(f176,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) ),
    inference(subsumption_resolution,[],[f175,f165])).

fof(f165,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(forward_demodulation,[],[f164,f141])).

fof(f141,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f132,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f131,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f107,f37])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f106,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f105,f32])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f33,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f164,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f163,f30])).

fof(f30,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f163,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f162,f28])).

fof(f28,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f159,f121])).

fof(f121,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f61,f64])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f35,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2,X3),u1_struct_0(sK3))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f108,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2,X3),u1_struct_0(sK3))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f97,f32])).

fof(f97,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2,X3),u1_struct_0(sK3))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X2) = X3 ) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(f175,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | ~ m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) ),
    inference(resolution,[],[f148,f27])).

fof(f27,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(forward_demodulation,[],[f147,f141])).

fof(f147,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f146,f30])).

% (13068)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f146,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f145,f28])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f142,f121])).

fof(f142,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f111,f29])).

fof(f111,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,X4,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK1))))
      | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4,X5),X4)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f110,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK1))))
      | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4,X5),X4)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f98,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK1))))
      | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4,X5),X4)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X4) = X5 ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f183,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) ),
    inference(forward_demodulation,[],[f182,f141])).

fof(f182,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f181,f30])).

fof(f181,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f180,f28])).

fof(f180,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f177,f121])).

fof(f177,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f113,f29])).

fof(f113,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7)) != k1_funct_1(X7,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = X7 ) ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f112,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7)) != k1_funct_1(X7,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = X7 ) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7)) != k1_funct_1(X7,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6,X7))
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = X7 ) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ~ sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f94,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f78,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f29,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f46,f56_D])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f56_D])).

fof(f56_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f93,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f92,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f77,f28])).

fof(f77,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | sP7(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f29,f56])).

%------------------------------------------------------------------------------
