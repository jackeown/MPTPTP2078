%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:06 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  222 (1879 expanded)
%              Number of leaves         :   24 ( 383 expanded)
%              Depth                    :   26
%              Number of atoms          : 1043 (16791 expanded)
%              Number of equality atoms :   78 (1814 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1522,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f472,f487,f538,f581,f608,f615,f1521])).

fof(f1521,plain,
    ( ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f1520])).

fof(f1520,plain,
    ( $false
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1519,f55])).

fof(f55,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f1519,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1518,f133])).

fof(f133,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f107,f129])).

fof(f129,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f114,f119])).

fof(f119,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f73,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1518,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(resolution,[],[f1513,f1283])).

fof(f1283,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f106,f1282])).

fof(f1282,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1281,f1138])).

fof(f1138,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1136,f129])).

fof(f1136,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_46 ),
    inference(resolution,[],[f1130,f124])).

fof(f124,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f119,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1130,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1129,f584])).

fof(f584,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f135,f533])).

fof(f533,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl7_46
  <=> k2_struct_0(sK2) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f135,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f132,f130])).

fof(f130,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f114,f118])).

fof(f118,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f116,f62])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f59,f128])).

fof(f128,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f1129,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1128,f161])).

fof(f161,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f142,f64])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f138,f69])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f87,f70])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f1128,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1127,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1127,plain,
    ( ! [X2] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1126,f119])).

fof(f1126,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1124,f585])).

fof(f585,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f136,f533])).

fof(f136,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f131,f130])).

fof(f131,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f58,f128])).

fof(f58,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1124,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(superposition,[],[f977,f129])).

fof(f977,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f976,f67])).

fof(f976,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f975,f66])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f975,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f957,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f957,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(superposition,[],[f951,f128])).

fof(f951,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f1281,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1278,f129])).

fof(f1278,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(resolution,[],[f1269,f466])).

fof(f466,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl7_42
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1269,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1268,f69])).

fof(f1268,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1267,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f1267,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1263,f70])).

fof(f1263,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl7_46 ),
    inference(resolution,[],[f1225,f62])).

fof(f1225,plain,
    ( ! [X6,X7] :
        ( ~ m1_pre_topc(sK3,X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ m1_pre_topc(X7,sK3)
        | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1224,f584])).

fof(f1224,plain,
    ( ! [X6,X7] :
        ( ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X7,sK3)
        | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1221,f585])).

fof(f1221,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X7,sK3)
        | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) )
    | ~ spl7_46 ),
    inference(superposition,[],[f1207,f583])).

fof(f583,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK2)
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f130,f533])).

fof(f1207,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f1206,f67])).

fof(f1206,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f1205,f66])).

fof(f1205,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f1199,f65])).

fof(f1199,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(superposition,[],[f1193,f128])).

fof(f1193,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1192,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f1192,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f81,f57])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f106,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f54,f53])).

fof(f54,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f1513,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1512,f1147])).

fof(f1147,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1146,f1138])).

fof(f1146,plain,
    ( k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1143,f129])).

fof(f1143,plain,
    ( k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(resolution,[],[f1135,f466])).

fof(f1135,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1134,f584])).

fof(f1134,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1133,f160])).

fof(f160,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f142,f62])).

fof(f1133,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1132,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f1132,plain,
    ( ! [X3] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1131,f118])).

fof(f1131,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1125,f585])).

fof(f1125,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl7_46 ),
    inference(superposition,[],[f977,f583])).

fof(f1512,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1511,f129])).

fof(f1511,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl7_41
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1510,f466])).

fof(f1510,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl7_41
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1508,f63])).

fof(f1508,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl7_41
    | ~ spl7_46 ),
    inference(resolution,[],[f1475,f463])).

fof(f463,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl7_41
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f1475,plain,
    ( ! [X6,X7] :
        ( ~ v1_tsep_1(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1474,f584])).

fof(f1474,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | v2_struct_0(X6)
        | ~ v1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1473,f118])).

fof(f1473,plain,
    ( ! [X6,X7] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | v2_struct_0(X6)
        | ~ v1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1472,f160])).

fof(f1472,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | v2_struct_0(X6)
        | ~ v1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1471,f61])).

fof(f1471,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | v2_struct_0(X6)
        | ~ v1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1465,f585])).

fof(f1465,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
        | v2_struct_0(X6)
        | ~ v1_tsep_1(X6,sK3)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
        | r1_tmap_1(sK3,sK1,sK4,X7) )
    | ~ spl7_46 ),
    inference(superposition,[],[f1443,f583])).

fof(f1443,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f1442,f66])).

fof(f1442,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f1441,f65])).

fof(f1441,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f1423,f67])).

fof(f1423,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(superposition,[],[f1417,f128])).

fof(f1417,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f1416,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f1416,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
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
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f615,plain,(
    spl7_42 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | spl7_42 ),
    inference(subsumption_resolution,[],[f613,f124])).

fof(f613,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_42 ),
    inference(resolution,[],[f467,f242])).

fof(f242,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f241,f134])).

fof(f134,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f60,f129])).

fof(f60,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f241,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f240,f129])).

fof(f240,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f234,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f119,f78])).

fof(f234,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f77,f119])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f467,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f465])).

fof(f608,plain,
    ( spl7_43
    | ~ spl7_45
    | ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | spl7_43
    | ~ spl7_45
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f597,f471])).

fof(f471,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | spl7_43 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl7_43
  <=> v3_pre_topc(k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f597,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ spl7_45
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f480,f533])).

fof(f480,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl7_45
  <=> v3_pre_topc(k2_struct_0(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f581,plain,(
    spl7_47 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl7_47 ),
    inference(subsumption_resolution,[],[f579,f537])).

fof(f537,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | spl7_47 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl7_47
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f579,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f577,f129])).

fof(f577,plain,(
    r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(resolution,[],[f523,f124])).

fof(f523,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) ) ),
    inference(resolution,[],[f519,f242])).

fof(f519,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) ) ),
    inference(forward_demodulation,[],[f516,f130])).

fof(f516,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f512,f62])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f508,f69])).

fof(f508,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f109,f70])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f89,f88])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f538,plain,
    ( spl7_46
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f529,f535,f531])).

fof(f529,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f528,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f528,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f526,f130])).

fof(f526,plain,(
    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f520,f200])).

fof(f200,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f198,f122])).

fof(f122,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f118,f75])).

fof(f198,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f197,f134])).

fof(f197,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f193,f129])).

fof(f193,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f80,f119])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f520,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f517,f129])).

fof(f517,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f512,f64])).

fof(f487,plain,(
    spl7_45 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl7_45 ),
    inference(subsumption_resolution,[],[f485,f160])).

fof(f485,plain,
    ( ~ v2_pre_topc(sK3)
    | spl7_45 ),
    inference(subsumption_resolution,[],[f484,f118])).

fof(f484,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl7_45 ),
    inference(resolution,[],[f481,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f481,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f479])).

fof(f472,plain,
    ( spl7_41
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f432,f469,f465,f461])).

fof(f432,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(superposition,[],[f267,f129])).

fof(f267,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f263,f160])).

fof(f263,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f110,f118])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f102,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (12249)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (12253)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (12260)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (12248)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (12267)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (12259)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (12252)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (12269)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (12251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (12270)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.26/0.52  % (12268)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.26/0.52  % (12257)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.52  % (12261)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.26/0.53  % (12256)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.26/0.53  % (12262)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.26/0.53  % (12272)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.26/0.53  % (12266)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.26/0.53  % (12264)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.26/0.53  % (12254)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.53  % (12247)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.26/0.53  % (12258)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.54  % (12250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.38/0.54  % (12252)Refutation not found, incomplete strategy% (12252)------------------------------
% 1.38/0.54  % (12252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (12252)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (12252)Memory used [KB]: 6396
% 1.38/0.54  % (12252)Time elapsed: 0.129 s
% 1.38/0.54  % (12252)------------------------------
% 1.38/0.54  % (12252)------------------------------
% 1.38/0.54  % (12263)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.38/0.54  % (12254)Refutation not found, incomplete strategy% (12254)------------------------------
% 1.38/0.54  % (12254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (12254)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (12254)Memory used [KB]: 1918
% 1.38/0.54  % (12254)Time elapsed: 0.096 s
% 1.38/0.54  % (12254)------------------------------
% 1.38/0.54  % (12254)------------------------------
% 1.38/0.55  % (12265)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.38/0.55  % (12255)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.56  % (12247)Refutation not found, incomplete strategy% (12247)------------------------------
% 1.38/0.56  % (12247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (12247)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (12247)Memory used [KB]: 10874
% 1.38/0.56  % (12247)Time elapsed: 0.144 s
% 1.38/0.56  % (12247)------------------------------
% 1.38/0.56  % (12247)------------------------------
% 1.38/0.56  % (12271)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.38/0.57  % (12269)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f1522,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(avatar_sat_refutation,[],[f472,f487,f538,f581,f608,f615,f1521])).
% 1.38/0.57  fof(f1521,plain,(
% 1.38/0.57    ~spl7_41 | ~spl7_42 | ~spl7_46),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f1520])).
% 1.38/0.57  fof(f1520,plain,(
% 1.38/0.57    $false | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(subsumption_resolution,[],[f1519,f55])).
% 1.38/0.57  fof(f55,plain,(
% 1.38/0.57    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f24,plain,(
% 1.38/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f23])).
% 1.38/0.57  fof(f23,plain,(
% 1.38/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f22])).
% 1.38/0.57  fof(f22,negated_conjecture,(
% 1.38/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.38/0.57    inference(negated_conjecture,[],[f21])).
% 1.38/0.57  fof(f21,conjecture,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.38/0.57  fof(f1519,plain,(
% 1.38/0.57    r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(subsumption_resolution,[],[f1518,f133])).
% 1.38/0.57  fof(f133,plain,(
% 1.38/0.57    m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.38/0.57    inference(backward_demodulation,[],[f107,f129])).
% 1.38/0.57  fof(f129,plain,(
% 1.38/0.57    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.38/0.57    inference(resolution,[],[f114,f119])).
% 1.38/0.57  fof(f119,plain,(
% 1.38/0.57    l1_pre_topc(sK2)),
% 1.38/0.57    inference(resolution,[],[f116,f64])).
% 1.38/0.57  fof(f64,plain,(
% 1.38/0.57    m1_pre_topc(sK2,sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f116,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 1.38/0.57    inference(resolution,[],[f78,f70])).
% 1.38/0.57  fof(f70,plain,(
% 1.38/0.57    l1_pre_topc(sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f78,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.38/0.57  fof(f114,plain,(
% 1.38/0.57    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.38/0.57    inference(resolution,[],[f73,f74])).
% 1.38/0.57  fof(f74,plain,(
% 1.38/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f6])).
% 1.38/0.57  fof(f6,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.38/0.57  fof(f73,plain,(
% 1.38/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.38/0.57  fof(f107,plain,(
% 1.38/0.57    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.38/0.57    inference(forward_demodulation,[],[f52,f53])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    sK5 = sK6),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f52,plain,(
% 1.38/0.57    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1518,plain,(
% 1.38/0.57    ~m1_subset_1(sK5,k2_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(resolution,[],[f1513,f1283])).
% 1.38/0.57  fof(f1283,plain,(
% 1.38/0.57    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(backward_demodulation,[],[f106,f1282])).
% 1.38/0.57  fof(f1282,plain,(
% 1.38/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1281,f1138])).
% 1.38/0.57  fof(f1138,plain,(
% 1.38/0.57    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) | ~spl7_46),
% 1.38/0.57    inference(forward_demodulation,[],[f1136,f129])).
% 1.38/0.57  fof(f1136,plain,(
% 1.38/0.57    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_46),
% 1.38/0.57    inference(resolution,[],[f1130,f124])).
% 1.38/0.57  fof(f124,plain,(
% 1.38/0.57    m1_pre_topc(sK2,sK2)),
% 1.38/0.57    inference(resolution,[],[f119,f75])).
% 1.38/0.57  fof(f75,plain,(
% 1.38/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f17])).
% 1.38/0.57  fof(f17,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.38/0.57  fof(f1130,plain,(
% 1.38/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1129,f584])).
% 1.38/0.57  fof(f584,plain,(
% 1.38/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~spl7_46),
% 1.38/0.57    inference(backward_demodulation,[],[f135,f533])).
% 1.38/0.57  fof(f533,plain,(
% 1.38/0.57    k2_struct_0(sK2) = k2_struct_0(sK3) | ~spl7_46),
% 1.38/0.57    inference(avatar_component_clause,[],[f531])).
% 1.38/0.57  fof(f531,plain,(
% 1.38/0.57    spl7_46 <=> k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.38/0.57  fof(f135,plain,(
% 1.38/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 1.38/0.57    inference(backward_demodulation,[],[f132,f130])).
% 1.38/0.57  fof(f130,plain,(
% 1.38/0.57    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.38/0.57    inference(resolution,[],[f114,f118])).
% 1.38/0.57  fof(f118,plain,(
% 1.38/0.57    l1_pre_topc(sK3)),
% 1.38/0.57    inference(resolution,[],[f116,f62])).
% 1.38/0.57  fof(f62,plain,(
% 1.38/0.57    m1_pre_topc(sK3,sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f132,plain,(
% 1.38/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 1.38/0.57    inference(backward_demodulation,[],[f59,f128])).
% 1.38/0.57  fof(f128,plain,(
% 1.38/0.57    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.38/0.57    inference(resolution,[],[f114,f67])).
% 1.38/0.57  fof(f67,plain,(
% 1.38/0.57    l1_pre_topc(sK1)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f59,plain,(
% 1.38/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1129,plain,(
% 1.38/0.57    ( ! [X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1128,f161])).
% 1.38/0.57  fof(f161,plain,(
% 1.38/0.57    v2_pre_topc(sK2)),
% 1.38/0.57    inference(resolution,[],[f142,f64])).
% 1.38/0.57  fof(f142,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f138,f69])).
% 1.38/0.57  fof(f69,plain,(
% 1.38/0.57    v2_pre_topc(sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f138,plain,(
% 1.38/0.57    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.38/0.57    inference(resolution,[],[f87,f70])).
% 1.38/0.57  fof(f87,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f43])).
% 1.38/0.57  fof(f43,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.57    inference(flattening,[],[f42])).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f4])).
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.38/0.57  fof(f1128,plain,(
% 1.38/0.57    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1127,f63])).
% 1.38/0.57  fof(f63,plain,(
% 1.38/0.57    ~v2_struct_0(sK2)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1127,plain,(
% 1.38/0.57    ( ! [X2] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1126,f119])).
% 1.38/0.57  fof(f1126,plain,(
% 1.38/0.57    ( ! [X2] : (~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1124,f585])).
% 1.38/0.57  fof(f585,plain,(
% 1.38/0.57    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~spl7_46),
% 1.38/0.57    inference(backward_demodulation,[],[f136,f533])).
% 1.38/0.57  fof(f136,plain,(
% 1.38/0.57    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 1.38/0.57    inference(backward_demodulation,[],[f131,f130])).
% 1.38/0.57  fof(f131,plain,(
% 1.38/0.57    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 1.38/0.57    inference(backward_demodulation,[],[f58,f128])).
% 1.38/0.57  fof(f58,plain,(
% 1.38/0.57    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1124,plain,(
% 1.38/0.57    ( ! [X2] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 1.38/0.57    inference(superposition,[],[f977,f129])).
% 1.38/0.57  fof(f977,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f976,f67])).
% 1.38/0.57  fof(f976,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~l1_pre_topc(X2) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f975,f66])).
% 1.38/0.57  fof(f66,plain,(
% 1.38/0.57    v2_pre_topc(sK1)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f975,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f957,f65])).
% 1.38/0.57  fof(f65,plain,(
% 1.38/0.57    ~v2_struct_0(sK1)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f957,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~l1_pre_topc(X2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(superposition,[],[f951,f128])).
% 1.38/0.57  fof(f951,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))) )),
% 1.38/0.57    inference(resolution,[],[f82,f57])).
% 1.38/0.57  fof(f57,plain,(
% 1.38/0.57    v1_funct_1(sK4)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f82,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f35])).
% 1.38/0.57  fof(f35,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f34])).
% 1.38/0.57  fof(f34,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f13])).
% 1.38/0.57  fof(f13,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.38/0.57  fof(f1281,plain,(
% 1.38/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1278,f129])).
% 1.38/0.57  fof(f1278,plain,(
% 1.38/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(resolution,[],[f1269,f466])).
% 1.38/0.57  fof(f466,plain,(
% 1.38/0.57    m1_pre_topc(sK2,sK3) | ~spl7_42),
% 1.38/0.57    inference(avatar_component_clause,[],[f465])).
% 1.38/0.57  fof(f465,plain,(
% 1.38/0.57    spl7_42 <=> m1_pre_topc(sK2,sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.38/0.57  fof(f1269,plain,(
% 1.38/0.57    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1268,f69])).
% 1.38/0.57  fof(f1268,plain,(
% 1.38/0.57    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1267,f68])).
% 1.38/0.57  fof(f68,plain,(
% 1.38/0.57    ~v2_struct_0(sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1267,plain,(
% 1.38/0.57    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1263,f70])).
% 1.38/0.57  fof(f1263,plain,(
% 1.38/0.57    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl7_46),
% 1.38/0.57    inference(resolution,[],[f1225,f62])).
% 1.38/0.57  fof(f1225,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1224,f584])).
% 1.38/0.57  fof(f1224,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1221,f585])).
% 1.38/0.57  fof(f1221,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) ) | ~spl7_46),
% 1.38/0.57    inference(superposition,[],[f1207,f583])).
% 1.38/0.57  fof(f583,plain,(
% 1.38/0.57    u1_struct_0(sK3) = k2_struct_0(sK2) | ~spl7_46),
% 1.38/0.57    inference(backward_demodulation,[],[f130,f533])).
% 1.38/0.57  fof(f1207,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1206,f67])).
% 1.38/0.57  fof(f1206,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_pre_topc(X4) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1205,f66])).
% 1.38/0.57  fof(f1205,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1199,f65])).
% 1.38/0.57  fof(f1199,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_pre_topc(X4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 1.38/0.57    inference(superposition,[],[f1193,f128])).
% 1.38/0.57  fof(f1193,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1192,f88])).
% 1.38/0.57  fof(f88,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f45])).
% 1.38/0.57  fof(f45,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.57    inference(flattening,[],[f44])).
% 1.38/0.57  fof(f44,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f20])).
% 1.38/0.57  fof(f20,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.38/0.57  fof(f1192,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(resolution,[],[f81,f57])).
% 1.38/0.57  fof(f81,plain,(
% 1.38/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  fof(f33,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f32])).
% 1.38/0.57  fof(f32,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f14])).
% 1.38/0.57  fof(f14,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.38/0.57  fof(f106,plain,(
% 1.38/0.57    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.38/0.57    inference(backward_demodulation,[],[f54,f53])).
% 1.38/0.57  fof(f54,plain,(
% 1.38/0.57    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1513,plain,(
% 1.38/0.57    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X0) | ~m1_subset_1(X0,k2_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1512,f1147])).
% 1.38/0.57  fof(f1147,plain,(
% 1.38/0.57    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1146,f1138])).
% 1.38/0.57  fof(f1146,plain,(
% 1.38/0.57    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1143,f129])).
% 1.38/0.57  fof(f1143,plain,(
% 1.38/0.57    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) | (~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(resolution,[],[f1135,f466])).
% 1.38/0.57  fof(f1135,plain,(
% 1.38/0.57    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1134,f584])).
% 1.38/0.57  fof(f1134,plain,(
% 1.38/0.57    ( ! [X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1133,f160])).
% 1.38/0.57  fof(f160,plain,(
% 1.38/0.57    v2_pre_topc(sK3)),
% 1.38/0.57    inference(resolution,[],[f142,f62])).
% 1.38/0.57  fof(f1133,plain,(
% 1.38/0.57    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1132,f61])).
% 1.38/0.57  fof(f61,plain,(
% 1.38/0.57    ~v2_struct_0(sK3)),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f1132,plain,(
% 1.38/0.57    ( ! [X3] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1131,f118])).
% 1.38/0.57  fof(f1131,plain,(
% 1.38/0.57    ( ! [X3] : (~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1125,f585])).
% 1.38/0.57  fof(f1125,plain,(
% 1.38/0.57    ( ! [X3] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl7_46),
% 1.38/0.57    inference(superposition,[],[f977,f583])).
% 1.38/0.57  fof(f1512,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(forward_demodulation,[],[f1511,f129])).
% 1.38/0.57  fof(f1511,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl7_41 | ~spl7_42 | ~spl7_46)),
% 1.38/0.57    inference(subsumption_resolution,[],[f1510,f466])).
% 1.38/0.57  fof(f1510,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl7_41 | ~spl7_46)),
% 1.38/0.57    inference(subsumption_resolution,[],[f1508,f63])).
% 1.38/0.57  fof(f1508,plain,(
% 1.38/0.57    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl7_41 | ~spl7_46)),
% 1.38/0.57    inference(resolution,[],[f1475,f463])).
% 1.38/0.57  fof(f463,plain,(
% 1.38/0.57    v1_tsep_1(sK2,sK3) | ~spl7_41),
% 1.38/0.57    inference(avatar_component_clause,[],[f461])).
% 1.38/0.57  fof(f461,plain,(
% 1.38/0.57    spl7_41 <=> v1_tsep_1(sK2,sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.38/0.57  fof(f1475,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~v1_tsep_1(X6,sK3) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1474,f584])).
% 1.38/0.57  fof(f1474,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1473,f118])).
% 1.38/0.57  fof(f1473,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1472,f160])).
% 1.38/0.57  fof(f1472,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1471,f61])).
% 1.38/0.57  fof(f1471,plain,(
% 1.38/0.57    ( ! [X6,X7] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(subsumption_resolution,[],[f1465,f585])).
% 1.38/0.57  fof(f1465,plain,(
% 1.38/0.57    ( ! [X6,X7] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) ) | ~spl7_46),
% 1.38/0.57    inference(superposition,[],[f1443,f583])).
% 1.38/0.57  fof(f1443,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1442,f66])).
% 1.38/0.57  fof(f1442,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1441,f65])).
% 1.38/0.57  fof(f1441,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1423,f67])).
% 1.38/0.57  fof(f1423,plain,(
% 1.38/0.57    ( ! [X4,X5,X3] : (~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 1.38/0.57    inference(superposition,[],[f1417,f128])).
% 1.38/0.57  fof(f1417,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f1416,f85])).
% 1.38/0.57  fof(f85,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f39])).
% 1.38/0.57  fof(f39,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f8])).
% 1.38/0.57  fof(f8,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.38/0.57  fof(f1416,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.38/0.57    inference(resolution,[],[f101,f57])).
% 1.38/0.57  fof(f101,plain,(
% 1.38/0.57    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) )),
% 1.38/0.57    inference(equality_resolution,[],[f83])).
% 1.38/0.57  fof(f83,plain,(
% 1.38/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f37])).
% 1.38/0.57  fof(f37,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f36])).
% 1.38/0.57  fof(f36,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f19])).
% 1.38/0.57  fof(f19,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 1.38/0.57  fof(f615,plain,(
% 1.38/0.57    spl7_42),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f614])).
% 1.38/0.57  fof(f614,plain,(
% 1.38/0.57    $false | spl7_42),
% 1.38/0.57    inference(subsumption_resolution,[],[f613,f124])).
% 1.38/0.57  fof(f613,plain,(
% 1.38/0.57    ~m1_pre_topc(sK2,sK2) | spl7_42),
% 1.38/0.57    inference(resolution,[],[f467,f242])).
% 1.38/0.57  fof(f242,plain,(
% 1.38/0.57    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(forward_demodulation,[],[f241,f134])).
% 1.38/0.57  fof(f134,plain,(
% 1.38/0.57    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 1.38/0.57    inference(backward_demodulation,[],[f60,f129])).
% 1.38/0.57  fof(f60,plain,(
% 1.38/0.57    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f241,plain,(
% 1.38/0.57    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(forward_demodulation,[],[f240,f129])).
% 1.38/0.57  fof(f240,plain,(
% 1.38/0.57    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f234,f123])).
% 1.38/0.57  fof(f123,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 1.38/0.57    inference(resolution,[],[f119,f78])).
% 1.38/0.57  fof(f234,plain,(
% 1.38/0.57    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(resolution,[],[f77,f119])).
% 1.38/0.57  fof(f77,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f28])).
% 1.38/0.57  fof(f28,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f11])).
% 1.38/0.57  fof(f11,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.38/0.57  fof(f467,plain,(
% 1.38/0.57    ~m1_pre_topc(sK2,sK3) | spl7_42),
% 1.38/0.57    inference(avatar_component_clause,[],[f465])).
% 1.38/0.57  fof(f608,plain,(
% 1.38/0.57    spl7_43 | ~spl7_45 | ~spl7_46),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f607])).
% 1.38/0.57  fof(f607,plain,(
% 1.38/0.57    $false | (spl7_43 | ~spl7_45 | ~spl7_46)),
% 1.38/0.57    inference(subsumption_resolution,[],[f597,f471])).
% 1.38/0.57  fof(f471,plain,(
% 1.38/0.57    ~v3_pre_topc(k2_struct_0(sK2),sK3) | spl7_43),
% 1.38/0.57    inference(avatar_component_clause,[],[f469])).
% 1.38/0.57  fof(f469,plain,(
% 1.38/0.57    spl7_43 <=> v3_pre_topc(k2_struct_0(sK2),sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 1.38/0.57  fof(f597,plain,(
% 1.38/0.57    v3_pre_topc(k2_struct_0(sK2),sK3) | (~spl7_45 | ~spl7_46)),
% 1.38/0.57    inference(backward_demodulation,[],[f480,f533])).
% 1.38/0.57  fof(f480,plain,(
% 1.38/0.57    v3_pre_topc(k2_struct_0(sK3),sK3) | ~spl7_45),
% 1.38/0.57    inference(avatar_component_clause,[],[f479])).
% 1.38/0.57  fof(f479,plain,(
% 1.38/0.57    spl7_45 <=> v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.38/0.57  fof(f581,plain,(
% 1.38/0.57    spl7_47),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f580])).
% 1.38/0.57  fof(f580,plain,(
% 1.38/0.57    $false | spl7_47),
% 1.38/0.57    inference(subsumption_resolution,[],[f579,f537])).
% 1.38/0.57  fof(f537,plain,(
% 1.38/0.57    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | spl7_47),
% 1.38/0.57    inference(avatar_component_clause,[],[f535])).
% 1.38/0.57  fof(f535,plain,(
% 1.38/0.57    spl7_47 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.38/0.57  fof(f579,plain,(
% 1.38/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))),
% 1.38/0.57    inference(forward_demodulation,[],[f577,f129])).
% 1.38/0.57  fof(f577,plain,(
% 1.38/0.57    r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))),
% 1.38/0.57    inference(resolution,[],[f523,f124])).
% 1.38/0.57  fof(f523,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))) )),
% 1.38/0.57    inference(resolution,[],[f519,f242])).
% 1.38/0.57  fof(f519,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))) )),
% 1.38/0.57    inference(forward_demodulation,[],[f516,f130])).
% 1.38/0.57  fof(f516,plain,(
% 1.38/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))) )),
% 1.38/0.57    inference(resolution,[],[f512,f62])).
% 1.38/0.57  fof(f512,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f508,f69])).
% 1.38/0.57  fof(f508,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.38/0.57    inference(resolution,[],[f109,f70])).
% 1.38/0.57  fof(f109,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f89,f88])).
% 1.38/0.57  fof(f89,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f47])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.57    inference(flattening,[],[f46])).
% 1.38/0.57  fof(f46,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f18])).
% 1.38/0.57  fof(f18,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.38/0.57  fof(f538,plain,(
% 1.38/0.57    spl7_46 | ~spl7_47),
% 1.38/0.57    inference(avatar_split_clause,[],[f529,f535,f531])).
% 1.38/0.57  fof(f529,plain,(
% 1.38/0.57    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.38/0.57    inference(resolution,[],[f528,f99])).
% 1.38/0.57  fof(f99,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.38/0.57    inference(cnf_transformation,[],[f1])).
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.57  fof(f528,plain,(
% 1.38/0.57    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.38/0.57    inference(forward_demodulation,[],[f526,f130])).
% 1.38/0.57  fof(f526,plain,(
% 1.38/0.57    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2))),
% 1.38/0.57    inference(resolution,[],[f520,f200])).
% 1.38/0.57  fof(f200,plain,(
% 1.38/0.57    m1_pre_topc(sK3,sK2)),
% 1.38/0.57    inference(resolution,[],[f198,f122])).
% 1.38/0.57  fof(f122,plain,(
% 1.38/0.57    m1_pre_topc(sK3,sK3)),
% 1.38/0.57    inference(resolution,[],[f118,f75])).
% 1.38/0.57  fof(f198,plain,(
% 1.38/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(forward_demodulation,[],[f197,f134])).
% 1.38/0.57  fof(f197,plain,(
% 1.38/0.57    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(forward_demodulation,[],[f193,f129])).
% 1.38/0.57  fof(f193,plain,(
% 1.38/0.57    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 1.38/0.57    inference(resolution,[],[f80,f119])).
% 1.38/0.57  fof(f80,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f31])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f9])).
% 1.38/0.57  fof(f9,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.38/0.57  fof(f520,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),k2_struct_0(sK2))) )),
% 1.38/0.57    inference(forward_demodulation,[],[f517,f129])).
% 1.38/0.57  fof(f517,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))) )),
% 1.38/0.57    inference(resolution,[],[f512,f64])).
% 1.38/0.57  fof(f487,plain,(
% 1.38/0.57    spl7_45),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f486])).
% 1.38/0.57  fof(f486,plain,(
% 1.38/0.57    $false | spl7_45),
% 1.38/0.57    inference(subsumption_resolution,[],[f485,f160])).
% 1.38/0.57  fof(f485,plain,(
% 1.38/0.57    ~v2_pre_topc(sK3) | spl7_45),
% 1.38/0.57    inference(subsumption_resolution,[],[f484,f118])).
% 1.38/0.57  fof(f484,plain,(
% 1.38/0.57    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl7_45),
% 1.38/0.57    inference(resolution,[],[f481,f86])).
% 1.38/0.57  fof(f86,plain,(
% 1.38/0.57    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f41])).
% 1.38/0.57  fof(f41,plain,(
% 1.38/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.57    inference(flattening,[],[f40])).
% 1.38/0.57  fof(f40,plain,(
% 1.38/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f12])).
% 1.38/0.57  fof(f12,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.38/0.57  fof(f481,plain,(
% 1.38/0.57    ~v3_pre_topc(k2_struct_0(sK3),sK3) | spl7_45),
% 1.38/0.57    inference(avatar_component_clause,[],[f479])).
% 1.38/0.57  fof(f472,plain,(
% 1.38/0.57    spl7_41 | ~spl7_42 | ~spl7_43),
% 1.38/0.57    inference(avatar_split_clause,[],[f432,f469,f465,f461])).
% 1.38/0.57  fof(f432,plain,(
% 1.38/0.57    ~v3_pre_topc(k2_struct_0(sK2),sK3) | ~m1_pre_topc(sK2,sK3) | v1_tsep_1(sK2,sK3)),
% 1.38/0.57    inference(superposition,[],[f267,f129])).
% 1.38/0.57  fof(f267,plain,(
% 1.38/0.57    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f263,f160])).
% 1.38/0.57  fof(f263,plain,(
% 1.38/0.57    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | ~v3_pre_topc(u1_struct_0(X3),sK3) | v1_tsep_1(X3,sK3)) )),
% 1.38/0.57    inference(resolution,[],[f110,f118])).
% 1.38/0.57  fof(f110,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f102,f79])).
% 1.38/0.57  fof(f79,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f30])).
% 1.38/0.57  fof(f30,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f16])).
% 1.38/0.57  fof(f16,axiom,(
% 1.38/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.38/0.57  fof(f102,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.38/0.57    inference(equality_resolution,[],[f92])).
% 1.38/0.57  fof(f92,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f49])).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.57    inference(flattening,[],[f48])).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f15])).
% 1.38/0.57  fof(f15,axiom,(
% 1.38/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (12269)------------------------------
% 1.38/0.57  % (12269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (12269)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (12269)Memory used [KB]: 11641
% 1.38/0.57  % (12269)Time elapsed: 0.163 s
% 1.38/0.57  % (12269)------------------------------
% 1.38/0.57  % (12269)------------------------------
% 1.38/0.59  % (12246)Success in time 0.233 s
%------------------------------------------------------------------------------
