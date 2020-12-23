%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:05 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  255 (1776 expanded)
%              Number of leaves         :   26 ( 350 expanded)
%              Depth                    :   33
%              Number of atoms          : 1397 (18605 expanded)
%              Number of equality atoms :   73 (1803 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f224,f267,f366,f372,f389,f393,f407,f838])).

fof(f838,plain,
    ( ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_21 ),
    inference(avatar_contradiction_clause,[],[f837])).

fof(f837,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f836,f50])).

fof(f50,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f20])).

% (25462)Refutation not found, incomplete strategy% (25462)------------------------------
% (25462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25462)Termination reason: Refutation not found, incomplete strategy

% (25462)Memory used [KB]: 10874
% (25462)Time elapsed: 0.168 s
% (25462)------------------------------
% (25462)------------------------------
% (25470)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f836,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f835,f114])).

fof(f114,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f835,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_21 ),
    inference(resolution,[],[f831,f818])).

fof(f818,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f817,f555])).

fof(f555,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f554,f552])).

fof(f552,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl10_9 ),
    inference(resolution,[],[f545,f129])).

fof(f129,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f124,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f124,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f121,f59])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f545,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f544,f270])).

fof(f270,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f54,f219])).

fof(f219,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl10_9
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f543,f155])).

fof(f155,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f136,f59])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f132,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f100,f65])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f543,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f542,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f542,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f541,f62])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f541,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f540,f61])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f540,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f539,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f539,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f536,f124])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl10_9 ),
    inference(resolution,[],[f535,f269])).

fof(f269,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f53,f219])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f535,plain,(
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
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f554,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f553,f219])).

fof(f553,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl10_9 ),
    inference(resolution,[],[f545,f210])).

fof(f210,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f209,f127])).

fof(f127,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f123,f68])).

fof(f123,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f121,f57])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f209,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f207,f55])).

fof(f55,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f207,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f94,f124])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f817,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f816,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f816,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    | v2_struct_0(sK3)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f815,f361])).

fof(f361,plain,
    ( v1_tsep_1(sK3,sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl10_16
  <=> v1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f815,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    | v2_struct_0(sK3)
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f814,f210])).

fof(f814,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    | v2_struct_0(sK3)
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f799,f114])).

fof(f799,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    | v2_struct_0(sK3)
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(superposition,[],[f796,f219])).

fof(f796,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | ~ v1_tsep_1(X0,sK2)
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),sK5)
        | v2_struct_0(X0) )
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(resolution,[],[f795,f754])).

fof(f754,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK2,sK1,sK4,X1)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | v2_struct_0(X0) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f753,f270])).

fof(f753,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f752,f61])).

fof(f752,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f751,f60])).

fof(f751,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f750,f124])).

fof(f750,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f749,f155])).

fof(f749,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f748,f58])).

fof(f748,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f745,f62])).

fof(f745,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | ~ r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(resolution,[],[f717,f269])).

fof(f717,plain,(
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
      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | ~ r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f716,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

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

fof(f716,plain,(
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
      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | ~ r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(resolution,[],[f107,f52])).

fof(f107,plain,(
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
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
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
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f795,plain,
    ( r1_tmap_1(sK2,sK1,sK4,sK5)
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f794,f114])).

fof(f794,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK1,sK4,sK5)
    | ~ spl10_9
    | ~ spl10_17
    | ~ spl10_21 ),
    inference(resolution,[],[f793,f715])).

fof(f715,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)
    | ~ spl10_9
    | ~ spl10_21 ),
    inference(backward_demodulation,[],[f113,f714])).

fof(f714,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2)
    | ~ spl10_9
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f711,f552])).

fof(f711,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl10_9
    | ~ spl10_21 ),
    inference(resolution,[],[f702,f402])).

fof(f402,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl10_21
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f702,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f701,f64])).

fof(f701,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f700,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f700,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f696,f65])).

fof(f696,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) )
    | ~ spl10_9 ),
    inference(resolution,[],[f692,f57])).

fof(f692,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f691,f270])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f690,f62])).

fof(f690,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f689,f61])).

fof(f689,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f687,f60])).

fof(f687,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4) )
    | ~ spl10_9 ),
    inference(resolution,[],[f592,f269])).

fof(f592,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(X1,X0,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X2)) )
    | ~ spl10_9 ),
    inference(superposition,[],[f590,f219])).

fof(f590,plain,(
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
    inference(subsumption_resolution,[],[f589,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f589,plain,(
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
    inference(resolution,[],[f95,f52])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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

fof(f113,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f793,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f792,f129])).

fof(f792,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f787,f58])).

fof(f787,plain,
    ( ! [X1] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9
    | ~ spl10_17 ),
    inference(resolution,[],[f779,f375])).

fof(f375,plain,
    ( v1_tsep_1(sK2,sK2)
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f373,f129])).

fof(f373,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_tsep_1(sK2,sK2)
    | ~ spl10_17 ),
    inference(resolution,[],[f364,f321])).

fof(f321,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f317,f155])).

fof(f317,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(resolution,[],[f116,f124])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f109,f91])).

fof(f91,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f364,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl10_17
  <=> v3_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f779,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f778,f270])).

fof(f778,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f777,f61])).

fof(f777,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f776,f60])).

fof(f776,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f775,f124])).

fof(f775,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f774,f155])).

fof(f774,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f773,f58])).

fof(f773,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f770,f62])).

fof(f770,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1)
        | r1_tmap_1(sK2,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(resolution,[],[f769,f269])).

fof(f769,plain,(
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
    inference(subsumption_resolution,[],[f768,f99])).

fof(f768,plain,(
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
    inference(resolution,[],[f108,f52])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f831,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f830,f581])).

fof(f581,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK3)
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f580,f552])).

fof(f580,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK3)
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f577,f219])).

fof(f577,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK1,sK4,sK3)
    | ~ spl10_9 ),
    inference(resolution,[],[f561,f127])).

fof(f561,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f560,f270])).

fof(f560,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f559,f62])).

fof(f559,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f558,f61])).

fof(f558,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f556,f60])).

fof(f556,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9 ),
    inference(resolution,[],[f548,f269])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f547,f154])).

fof(f154,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f136,f57])).

fof(f547,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f546,f56])).

fof(f546,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1)) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f537,f123])).

fof(f537,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ m1_pre_topc(X1,sK3)
        | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1)) )
    | ~ spl10_9 ),
    inference(superposition,[],[f535,f219])).

fof(f830,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f829,f219])).

fof(f829,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f828,f127])).

fof(f828,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f826,f56])).

fof(f826,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(resolution,[],[f825,f384])).

fof(f384,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl10_18
  <=> v1_tsep_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f824,f270])).

fof(f824,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f823,f61])).

fof(f823,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f822,f60])).

fof(f822,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f820,f62])).

fof(f820,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl10_9 ),
    inference(resolution,[],[f782,f269])).

fof(f782,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f781,f123])).

fof(f781,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f780,f154])).

fof(f780,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f771,f56])).

fof(f771,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_9 ),
    inference(superposition,[],[f769,f219])).

fof(f407,plain,(
    spl10_21 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl10_21 ),
    inference(subsumption_resolution,[],[f405,f129])).

fof(f405,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl10_21 ),
    inference(resolution,[],[f403,f255])).

fof(f255,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f254,f55])).

fof(f254,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f250,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f124,f89])).

fof(f250,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f88,f124])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f403,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f401])).

fof(f393,plain,
    ( ~ spl10_9
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl10_9
    | spl10_19 ),
    inference(subsumption_resolution,[],[f391,f115])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f67,f66])).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f391,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_9
    | spl10_19 ),
    inference(subsumption_resolution,[],[f390,f285])).

fof(f285,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f284,f154])).

fof(f284,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f283,f123])).

fof(f283,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_9 ),
    inference(superposition,[],[f86,f219])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f390,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_9
    | spl10_19 ),
    inference(resolution,[],[f388,f301])).

fof(f301,plain,
    ( ! [X3] :
        ( v3_pre_topc(X3,sK3)
        | ~ r2_hidden(X3,u1_pre_topc(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f300,f219])).

fof(f300,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK3))
      | v3_pre_topc(X3,sK3) ) ),
    inference(resolution,[],[f92,f123])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f388,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl10_19
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f389,plain,
    ( spl10_18
    | ~ spl10_19
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f380,f217,f386,f382])).

fof(f380,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | v1_tsep_1(sK3,sK3)
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f378,f127])).

fof(f378,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v1_tsep_1(sK3,sK3)
    | ~ spl10_9 ),
    inference(superposition,[],[f322,f219])).

fof(f322,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f318,f154])).

fof(f318,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f116,f123])).

fof(f372,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl10_17 ),
    inference(subsumption_resolution,[],[f370,f155])).

fof(f370,plain,
    ( ~ v2_pre_topc(sK2)
    | spl10_17 ),
    inference(subsumption_resolution,[],[f369,f124])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl10_17 ),
    inference(resolution,[],[f368,f86])).

fof(f368,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl10_17 ),
    inference(subsumption_resolution,[],[f367,f115])).

fof(f367,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_17 ),
    inference(resolution,[],[f365,f299])).

fof(f299,plain,(
    ! [X2] :
      ( v3_pre_topc(X2,sK2)
      | ~ r2_hidden(X2,u1_pre_topc(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f92,f124])).

fof(f365,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f363])).

fof(f366,plain,
    ( spl10_16
    | ~ spl10_17
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f357,f217,f363,f359])).

fof(f357,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | v1_tsep_1(sK3,sK2)
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f355,f210])).

fof(f355,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v1_tsep_1(sK3,sK2)
    | ~ spl10_9 ),
    inference(superposition,[],[f321,f219])).

fof(f267,plain,(
    spl10_10 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl10_10 ),
    inference(subsumption_resolution,[],[f264,f223])).

fof(f223,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl10_10
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f264,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f259,f129])).

fof(f259,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | r1_tarski(u1_struct_0(X2),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f255,f168])).

fof(f168,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | r1_tarski(u1_struct_0(X3),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f90,f123])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f224,plain,
    ( spl10_9
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f215,f221,f217])).

fof(f215,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(resolution,[],[f212,f106])).

fof(f106,plain,(
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

fof(f212,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f210,f167])).

fof(f167,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f90,f124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25468)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (25477)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (25476)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.39/0.54  % (25466)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.39/0.54  % (25473)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.54  % (25480)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.55  % (25465)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.39/0.55  % (25463)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.55  % (25464)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.55  % (25469)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.39/0.55  % (25484)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.49/0.55  % (25467)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.49/0.56  % (25472)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.49/0.56  % (25462)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.49/0.56  % (25487)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.49/0.56  % (25474)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.49/0.56  % (25467)Refutation not found, incomplete strategy% (25467)------------------------------
% 1.49/0.56  % (25467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (25467)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (25467)Memory used [KB]: 6268
% 1.49/0.56  % (25467)Time elapsed: 0.139 s
% 1.49/0.56  % (25467)------------------------------
% 1.49/0.56  % (25467)------------------------------
% 1.49/0.56  % (25486)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.56  % (25479)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.56  % (25475)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.49/0.56  % (25469)Refutation not found, incomplete strategy% (25469)------------------------------
% 1.49/0.56  % (25469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (25469)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (25469)Memory used [KB]: 1918
% 1.49/0.56  % (25469)Time elapsed: 0.092 s
% 1.49/0.56  % (25469)------------------------------
% 1.49/0.56  % (25469)------------------------------
% 1.49/0.57  % (25485)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.49/0.57  % (25483)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.49/0.57  % (25471)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.49/0.57  % (25482)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.49/0.58  % (25478)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.49/0.58  % (25481)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.49/0.59  % (25484)Refutation found. Thanks to Tanya!
% 1.49/0.59  % SZS status Theorem for theBenchmark
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f839,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(avatar_sat_refutation,[],[f224,f267,f366,f372,f389,f393,f407,f838])).
% 1.49/0.59  fof(f838,plain,(
% 1.49/0.59    ~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_21),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f837])).
% 1.49/0.59  fof(f837,plain,(
% 1.49/0.59    $false | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f836,f50])).
% 1.49/0.59  fof(f50,plain,(
% 1.49/0.59    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f23,plain,(
% 1.49/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.59    inference(flattening,[],[f22])).
% 1.49/0.59  fof(f22,plain,(
% 1.49/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f20])).
% 1.49/0.59  % (25462)Refutation not found, incomplete strategy% (25462)------------------------------
% 1.49/0.59  % (25462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (25462)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (25462)Memory used [KB]: 10874
% 1.49/0.59  % (25462)Time elapsed: 0.168 s
% 1.49/0.59  % (25462)------------------------------
% 1.49/0.59  % (25462)------------------------------
% 1.49/0.59  % (25470)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.49/0.59  fof(f20,negated_conjecture,(
% 1.49/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.49/0.59    inference(negated_conjecture,[],[f19])).
% 1.49/0.59  fof(f19,conjecture,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.49/0.59  fof(f836,plain,(
% 1.49/0.59    r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f835,f114])).
% 1.49/0.59  fof(f114,plain,(
% 1.49/0.59    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.49/0.59    inference(forward_demodulation,[],[f47,f48])).
% 1.49/0.59  fof(f48,plain,(
% 1.49/0.59    sK5 = sK6),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f47,plain,(
% 1.49/0.59    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f835,plain,(
% 1.49/0.59    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_21)),
% 1.49/0.59    inference(resolution,[],[f831,f818])).
% 1.49/0.59  fof(f818,plain,(
% 1.49/0.59    r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(forward_demodulation,[],[f817,f555])).
% 1.49/0.59  fof(f555,plain,(
% 1.49/0.59    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~spl10_9),
% 1.49/0.59    inference(forward_demodulation,[],[f554,f552])).
% 1.49/0.59  fof(f552,plain,(
% 1.49/0.59    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f545,f129])).
% 1.49/0.59  fof(f129,plain,(
% 1.49/0.59    m1_pre_topc(sK2,sK2)),
% 1.49/0.59    inference(resolution,[],[f124,f68])).
% 1.49/0.59  fof(f68,plain,(
% 1.49/0.59    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f24])).
% 1.49/0.59  fof(f24,plain,(
% 1.49/0.59    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f15])).
% 1.49/0.59  fof(f15,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.49/0.59  fof(f124,plain,(
% 1.49/0.59    l1_pre_topc(sK2)),
% 1.49/0.59    inference(resolution,[],[f121,f59])).
% 1.49/0.59  fof(f59,plain,(
% 1.49/0.59    m1_pre_topc(sK2,sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f121,plain,(
% 1.49/0.59    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 1.49/0.59    inference(resolution,[],[f89,f65])).
% 1.49/0.59  fof(f65,plain,(
% 1.49/0.59    l1_pre_topc(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f89,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f28])).
% 1.49/0.59  fof(f28,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f7])).
% 1.49/0.59  fof(f7,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.49/0.59  fof(f545,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f544,f270])).
% 1.49/0.59  fof(f270,plain,(
% 1.49/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl10_9),
% 1.49/0.59    inference(backward_demodulation,[],[f54,f219])).
% 1.49/0.59  fof(f219,plain,(
% 1.49/0.59    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl10_9),
% 1.49/0.59    inference(avatar_component_clause,[],[f217])).
% 1.49/0.59  fof(f217,plain,(
% 1.49/0.59    spl10_9 <=> u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.49/0.59  fof(f54,plain,(
% 1.49/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f544,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f543,f155])).
% 1.49/0.59  fof(f155,plain,(
% 1.49/0.59    v2_pre_topc(sK2)),
% 1.49/0.59    inference(resolution,[],[f136,f59])).
% 1.49/0.59  fof(f136,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f132,f64])).
% 1.49/0.59  fof(f64,plain,(
% 1.49/0.59    v2_pre_topc(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f132,plain,(
% 1.49/0.59    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.49/0.59    inference(resolution,[],[f100,f65])).
% 1.49/0.59  fof(f100,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f42])).
% 1.49/0.59  fof(f42,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f41])).
% 1.49/0.59  fof(f41,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.49/0.59  fof(f543,plain,(
% 1.49/0.59    ( ! [X0] : (~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f542,f58])).
% 1.49/0.59  fof(f58,plain,(
% 1.49/0.59    ~v2_struct_0(sK2)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f542,plain,(
% 1.49/0.59    ( ! [X0] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f541,f62])).
% 1.49/0.59  fof(f62,plain,(
% 1.49/0.59    l1_pre_topc(sK1)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f541,plain,(
% 1.49/0.59    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f540,f61])).
% 1.49/0.59  fof(f61,plain,(
% 1.49/0.59    v2_pre_topc(sK1)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f540,plain,(
% 1.49/0.59    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f539,f60])).
% 1.49/0.59  fof(f60,plain,(
% 1.49/0.59    ~v2_struct_0(sK1)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f539,plain,(
% 1.49/0.59    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f536,f124])).
% 1.49/0.59  fof(f536,plain,(
% 1.49/0.59    ( ! [X0] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f535,f269])).
% 1.49/0.59  fof(f269,plain,(
% 1.49/0.59    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl10_9),
% 1.49/0.59    inference(backward_demodulation,[],[f53,f219])).
% 1.49/0.59  fof(f53,plain,(
% 1.49/0.59    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f535,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))) )),
% 1.49/0.59    inference(resolution,[],[f96,f52])).
% 1.49/0.59  fof(f52,plain,(
% 1.49/0.59    v1_funct_1(sK4)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f96,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f36])).
% 1.49/0.59  fof(f36,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.59    inference(flattening,[],[f35])).
% 1.49/0.59  fof(f35,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f11])).
% 1.49/0.59  fof(f11,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.49/0.59  fof(f554,plain,(
% 1.49/0.59    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~spl10_9),
% 1.49/0.59    inference(forward_demodulation,[],[f553,f219])).
% 1.49/0.59  fof(f553,plain,(
% 1.49/0.59    k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f545,f210])).
% 1.49/0.59  fof(f210,plain,(
% 1.49/0.59    m1_pre_topc(sK3,sK2)),
% 1.49/0.59    inference(resolution,[],[f209,f127])).
% 1.49/0.59  fof(f127,plain,(
% 1.49/0.59    m1_pre_topc(sK3,sK3)),
% 1.49/0.59    inference(resolution,[],[f123,f68])).
% 1.49/0.59  fof(f123,plain,(
% 1.49/0.59    l1_pre_topc(sK3)),
% 1.49/0.59    inference(resolution,[],[f121,f57])).
% 1.49/0.59  fof(f57,plain,(
% 1.49/0.59    m1_pre_topc(sK3,sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f209,plain,(
% 1.49/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 1.49/0.59    inference(forward_demodulation,[],[f207,f55])).
% 1.49/0.59  fof(f55,plain,(
% 1.49/0.59    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f207,plain,(
% 1.49/0.59    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 1.49/0.59    inference(resolution,[],[f94,f124])).
% 1.49/0.59  fof(f94,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f32])).
% 1.49/0.59  fof(f32,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f9])).
% 1.49/0.59  fof(f9,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.49/0.59  fof(f817,plain,(
% 1.49/0.59    r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5) | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f816,f56])).
% 1.49/0.59  fof(f56,plain,(
% 1.49/0.59    ~v2_struct_0(sK3)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f816,plain,(
% 1.49/0.59    r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5) | v2_struct_0(sK3) | (~spl10_9 | ~spl10_16 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f815,f361])).
% 1.49/0.59  fof(f361,plain,(
% 1.49/0.59    v1_tsep_1(sK3,sK2) | ~spl10_16),
% 1.49/0.59    inference(avatar_component_clause,[],[f359])).
% 1.49/0.59  fof(f359,plain,(
% 1.49/0.59    spl10_16 <=> v1_tsep_1(sK3,sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.49/0.59  fof(f815,plain,(
% 1.49/0.59    ~v1_tsep_1(sK3,sK2) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5) | v2_struct_0(sK3) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f814,f210])).
% 1.49/0.59  fof(f814,plain,(
% 1.49/0.59    ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5) | v2_struct_0(sK3) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f799,f114])).
% 1.49/0.59  fof(f799,plain,(
% 1.49/0.59    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK3),sK5) | v2_struct_0(sK3) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(superposition,[],[f796,f219])).
% 1.49/0.59  fof(f796,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | ~v1_tsep_1(X0,sK2) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),sK5) | v2_struct_0(X0)) ) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(resolution,[],[f795,f754])).
% 1.49/0.59  fof(f754,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tmap_1(sK2,sK1,sK4,X1) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | v2_struct_0(X0)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f753,f270])).
% 1.49/0.59  fof(f753,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f752,f61])).
% 1.49/0.59  fof(f752,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f751,f60])).
% 1.49/0.59  fof(f751,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f750,f124])).
% 1.49/0.59  fof(f750,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f749,f155])).
% 1.49/0.59  fof(f749,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f748,f58])).
% 1.49/0.59  fof(f748,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f745,f62])).
% 1.49/0.59  fof(f745,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | ~r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f717,f269])).
% 1.49/0.59  fof(f717,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | ~r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f716,f99])).
% 1.49/0.59  fof(f99,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f40])).
% 1.49/0.59  fof(f40,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.59    inference(flattening,[],[f39])).
% 1.49/0.59  fof(f39,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.49/0.59  fof(f716,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | ~r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.49/0.59    inference(resolution,[],[f107,f52])).
% 1.49/0.59  fof(f107,plain,(
% 1.49/0.59    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 1.49/0.59    inference(equality_resolution,[],[f98])).
% 1.49/0.59  fof(f98,plain,(
% 1.49/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f38])).
% 1.49/0.59  fof(f38,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.59    inference(flattening,[],[f37])).
% 1.49/0.59  fof(f37,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f17])).
% 1.49/0.59  fof(f17,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 1.49/0.59  fof(f795,plain,(
% 1.49/0.59    r1_tmap_1(sK2,sK1,sK4,sK5) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(subsumption_resolution,[],[f794,f114])).
% 1.49/0.59  fof(f794,plain,(
% 1.49/0.59    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK4,sK5) | (~spl10_9 | ~spl10_17 | ~spl10_21)),
% 1.49/0.59    inference(resolution,[],[f793,f715])).
% 1.49/0.59  fof(f715,plain,(
% 1.49/0.59    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) | (~spl10_9 | ~spl10_21)),
% 1.49/0.59    inference(backward_demodulation,[],[f113,f714])).
% 1.49/0.59  fof(f714,plain,(
% 1.49/0.59    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2) | (~spl10_9 | ~spl10_21)),
% 1.49/0.59    inference(forward_demodulation,[],[f711,f552])).
% 1.49/0.59  fof(f711,plain,(
% 1.49/0.59    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl10_9 | ~spl10_21)),
% 1.49/0.59    inference(resolution,[],[f702,f402])).
% 1.49/0.59  fof(f402,plain,(
% 1.49/0.59    m1_pre_topc(sK2,sK3) | ~spl10_21),
% 1.49/0.59    inference(avatar_component_clause,[],[f401])).
% 1.49/0.59  fof(f401,plain,(
% 1.49/0.59    spl10_21 <=> m1_pre_topc(sK2,sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.49/0.59  fof(f702,plain,(
% 1.49/0.59    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f701,f64])).
% 1.49/0.59  fof(f701,plain,(
% 1.49/0.59    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f700,f63])).
% 1.49/0.59  fof(f63,plain,(
% 1.49/0.59    ~v2_struct_0(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f700,plain,(
% 1.49/0.59    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f696,f65])).
% 1.49/0.59  fof(f696,plain,(
% 1.49/0.59    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f692,f57])).
% 1.49/0.59  fof(f692,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f691,f270])).
% 1.49/0.59  fof(f691,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f690,f62])).
% 1.49/0.59  fof(f690,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f689,f61])).
% 1.49/0.59  fof(f689,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f687,f60])).
% 1.49/0.59  fof(f687,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK3,X1,sK4)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f592,f269])).
% 1.49/0.59  fof(f592,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,X0,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X2))) ) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f590,f219])).
% 1.49/0.59  fof(f590,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f589,f101])).
% 1.49/0.59  fof(f101,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f44])).
% 1.49/0.59  fof(f44,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f43])).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f18])).
% 1.49/0.59  fof(f18,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.49/0.59  fof(f589,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.49/0.59    inference(resolution,[],[f95,f52])).
% 1.49/0.59  fof(f95,plain,(
% 1.49/0.59    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f34])).
% 1.49/0.59  fof(f34,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.59    inference(flattening,[],[f33])).
% 1.49/0.59  fof(f33,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f12])).
% 1.49/0.59  fof(f12,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.49/0.59  fof(f113,plain,(
% 1.49/0.59    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.49/0.59    inference(backward_demodulation,[],[f49,f48])).
% 1.49/0.59  fof(f49,plain,(
% 1.49/0.59    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f793,plain,(
% 1.49/0.59    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | (~spl10_9 | ~spl10_17)),
% 1.49/0.59    inference(subsumption_resolution,[],[f792,f129])).
% 1.49/0.59  fof(f792,plain,(
% 1.49/0.59    ( ! [X1] : (~m1_pre_topc(sK2,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | (~spl10_9 | ~spl10_17)),
% 1.49/0.59    inference(subsumption_resolution,[],[f787,f58])).
% 1.49/0.59  fof(f787,plain,(
% 1.49/0.59    ( ! [X1] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | (~spl10_9 | ~spl10_17)),
% 1.49/0.59    inference(resolution,[],[f779,f375])).
% 1.49/0.59  fof(f375,plain,(
% 1.49/0.59    v1_tsep_1(sK2,sK2) | ~spl10_17),
% 1.49/0.59    inference(subsumption_resolution,[],[f373,f129])).
% 1.49/0.59  fof(f373,plain,(
% 1.49/0.59    ~m1_pre_topc(sK2,sK2) | v1_tsep_1(sK2,sK2) | ~spl10_17),
% 1.49/0.59    inference(resolution,[],[f364,f321])).
% 1.49/0.59  fof(f321,plain,(
% 1.49/0.59    ( ! [X2] : (~v3_pre_topc(u1_struct_0(X2),sK2) | ~m1_pre_topc(X2,sK2) | v1_tsep_1(X2,sK2)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f317,f155])).
% 1.49/0.59  fof(f317,plain,(
% 1.49/0.59    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | ~v3_pre_topc(u1_struct_0(X2),sK2) | v1_tsep_1(X2,sK2)) )),
% 1.49/0.59    inference(resolution,[],[f116,f124])).
% 1.49/0.59  fof(f116,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f109,f91])).
% 1.49/0.59  fof(f91,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f30])).
% 1.49/0.59  fof(f30,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.49/0.59  fof(f109,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.49/0.59    inference(equality_resolution,[],[f103])).
% 1.49/0.59  fof(f103,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f46])).
% 1.49/0.59  fof(f46,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f45])).
% 1.49/0.59  fof(f45,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f13])).
% 1.49/0.59  fof(f13,axiom,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.49/0.59  fof(f364,plain,(
% 1.49/0.59    v3_pre_topc(u1_struct_0(sK2),sK2) | ~spl10_17),
% 1.49/0.59    inference(avatar_component_clause,[],[f363])).
% 1.49/0.59  fof(f363,plain,(
% 1.49/0.59    spl10_17 <=> v3_pre_topc(u1_struct_0(sK2),sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.49/0.59  fof(f779,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_tsep_1(X0,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f778,f270])).
% 1.49/0.59  fof(f778,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f777,f61])).
% 1.49/0.59  fof(f777,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f776,f60])).
% 1.49/0.59  fof(f776,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f775,f124])).
% 1.49/0.59  fof(f775,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f774,f155])).
% 1.49/0.59  fof(f774,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f773,f58])).
% 1.49/0.59  fof(f773,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f770,f62])).
% 1.49/0.59  fof(f770,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK4,X0),X1) | r1_tmap_1(sK2,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f769,f269])).
% 1.49/0.59  fof(f769,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f768,f99])).
% 1.49/0.59  fof(f768,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 1.49/0.59    inference(resolution,[],[f108,f52])).
% 1.49/0.59  fof(f108,plain,(
% 1.49/0.59    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) )),
% 1.49/0.59    inference(equality_resolution,[],[f97])).
% 1.49/0.59  fof(f97,plain,(
% 1.49/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f38])).
% 1.49/0.59  fof(f831,plain,(
% 1.49/0.59    ( ! [X0] : (~r1_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_9 | ~spl10_18)),
% 1.49/0.59    inference(forward_demodulation,[],[f830,f581])).
% 1.49/0.59  fof(f581,plain,(
% 1.49/0.59    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK3) | ~spl10_9),
% 1.49/0.59    inference(forward_demodulation,[],[f580,f552])).
% 1.49/0.59  fof(f580,plain,(
% 1.49/0.59    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK3) | ~spl10_9),
% 1.49/0.59    inference(forward_demodulation,[],[f577,f219])).
% 1.49/0.59  fof(f577,plain,(
% 1.49/0.59    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK1,sK4,sK3) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f561,f127])).
% 1.49/0.59  fof(f561,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f560,f270])).
% 1.49/0.59  fof(f560,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f559,f62])).
% 1.49/0.59  fof(f559,plain,(
% 1.49/0.59    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f558,f61])).
% 1.49/0.59  fof(f558,plain,(
% 1.49/0.59    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f556,f60])).
% 1.49/0.59  fof(f556,plain,(
% 1.49/0.59    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f548,f269])).
% 1.49/0.59  fof(f548,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f547,f154])).
% 1.49/0.59  fof(f154,plain,(
% 1.49/0.59    v2_pre_topc(sK3)),
% 1.49/0.59    inference(resolution,[],[f136,f57])).
% 1.49/0.59  fof(f547,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f546,f56])).
% 1.49/0.59  fof(f546,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1))) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f537,f123])).
% 1.49/0.59  fof(f537,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k2_tmap_1(sK3,X0,sK4,X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0),sK4,u1_struct_0(X1))) ) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f535,f219])).
% 1.49/0.59  fof(f830,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_9 | ~spl10_18)),
% 1.49/0.59    inference(forward_demodulation,[],[f829,f219])).
% 1.49/0.59  fof(f829,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_9 | ~spl10_18)),
% 1.49/0.59    inference(subsumption_resolution,[],[f828,f127])).
% 1.49/0.59  fof(f828,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_pre_topc(sK3,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_9 | ~spl10_18)),
% 1.49/0.59    inference(subsumption_resolution,[],[f826,f56])).
% 1.49/0.59  fof(f826,plain,(
% 1.49/0.59    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_9 | ~spl10_18)),
% 1.49/0.59    inference(resolution,[],[f825,f384])).
% 1.49/0.59  fof(f384,plain,(
% 1.49/0.59    v1_tsep_1(sK3,sK3) | ~spl10_18),
% 1.49/0.59    inference(avatar_component_clause,[],[f382])).
% 1.49/0.59  fof(f382,plain,(
% 1.49/0.59    spl10_18 <=> v1_tsep_1(sK3,sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.49/0.59  fof(f825,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_tsep_1(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f824,f270])).
% 1.49/0.59  fof(f824,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f823,f61])).
% 1.49/0.59  fof(f823,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f822,f60])).
% 1.49/0.59  fof(f822,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f820,f62])).
% 1.49/0.59  fof(f820,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | ~spl10_9),
% 1.49/0.59    inference(resolution,[],[f782,f269])).
% 1.49/0.59  fof(f782,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) | r1_tmap_1(sK3,X0,sK4,X2)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f781,f123])).
% 1.49/0.59  fof(f781,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) | r1_tmap_1(sK3,X0,sK4,X2)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f780,f154])).
% 1.49/0.59  fof(f780,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) | r1_tmap_1(sK3,X0,sK4,X2)) ) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f771,f56])).
% 1.49/0.59  fof(f771,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) | r1_tmap_1(sK3,X0,sK4,X2)) ) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f769,f219])).
% 1.49/0.59  fof(f407,plain,(
% 1.49/0.59    spl10_21),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f406])).
% 1.49/0.59  fof(f406,plain,(
% 1.49/0.59    $false | spl10_21),
% 1.49/0.59    inference(subsumption_resolution,[],[f405,f129])).
% 1.49/0.59  fof(f405,plain,(
% 1.49/0.59    ~m1_pre_topc(sK2,sK2) | spl10_21),
% 1.49/0.59    inference(resolution,[],[f403,f255])).
% 1.49/0.59  fof(f255,plain,(
% 1.49/0.59    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 1.49/0.59    inference(forward_demodulation,[],[f254,f55])).
% 1.49/0.59  fof(f254,plain,(
% 1.49/0.59    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f250,f128])).
% 1.49/0.59  fof(f128,plain,(
% 1.49/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 1.49/0.59    inference(resolution,[],[f124,f89])).
% 1.49/0.59  fof(f250,plain,(
% 1.49/0.59    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.49/0.59    inference(resolution,[],[f88,f124])).
% 1.49/0.59  fof(f88,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f27])).
% 1.49/0.59  fof(f27,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f10])).
% 1.49/0.59  fof(f10,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.49/0.59  fof(f403,plain,(
% 1.49/0.59    ~m1_pre_topc(sK2,sK3) | spl10_21),
% 1.49/0.59    inference(avatar_component_clause,[],[f401])).
% 1.49/0.59  fof(f393,plain,(
% 1.49/0.59    ~spl10_9 | spl10_19),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f392])).
% 1.49/0.59  fof(f392,plain,(
% 1.49/0.59    $false | (~spl10_9 | spl10_19)),
% 1.49/0.59    inference(subsumption_resolution,[],[f391,f115])).
% 1.49/0.59  fof(f115,plain,(
% 1.49/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(forward_demodulation,[],[f67,f66])).
% 1.49/0.59  fof(f66,plain,(
% 1.49/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f2])).
% 1.49/0.59  fof(f2,axiom,(
% 1.49/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.49/0.59  fof(f67,plain,(
% 1.49/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f3])).
% 1.49/0.59  fof(f3,axiom,(
% 1.49/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.49/0.59  fof(f391,plain,(
% 1.49/0.59    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl10_9 | spl10_19)),
% 1.49/0.59    inference(subsumption_resolution,[],[f390,f285])).
% 1.49/0.59  fof(f285,plain,(
% 1.49/0.59    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f284,f154])).
% 1.49/0.59  fof(f284,plain,(
% 1.49/0.59    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~v2_pre_topc(sK3) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f283,f123])).
% 1.49/0.59  fof(f283,plain,(
% 1.49/0.59    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f86,f219])).
% 1.49/0.59  fof(f86,plain,(
% 1.49/0.59    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f26])).
% 1.49/0.59  fof(f26,plain,(
% 1.49/0.59    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f25])).
% 1.49/0.59  fof(f25,plain,(
% 1.49/0.59    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.49/0.59    inference(rectify,[],[f5])).
% 1.49/0.59  fof(f5,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.49/0.59  fof(f390,plain,(
% 1.49/0.59    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl10_9 | spl10_19)),
% 1.49/0.59    inference(resolution,[],[f388,f301])).
% 1.49/0.59  fof(f301,plain,(
% 1.49/0.59    ( ! [X3] : (v3_pre_topc(X3,sK3) | ~r2_hidden(X3,u1_pre_topc(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl10_9),
% 1.49/0.59    inference(forward_demodulation,[],[f300,f219])).
% 1.49/0.59  fof(f300,plain,(
% 1.49/0.59    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(X3,u1_pre_topc(sK3)) | v3_pre_topc(X3,sK3)) )),
% 1.49/0.59    inference(resolution,[],[f92,f123])).
% 1.49/0.59  fof(f92,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f31])).
% 1.49/0.59  fof(f31,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.49/0.59  fof(f388,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK3) | spl10_19),
% 1.49/0.59    inference(avatar_component_clause,[],[f386])).
% 1.49/0.59  fof(f386,plain,(
% 1.49/0.59    spl10_19 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.49/0.59  fof(f389,plain,(
% 1.49/0.59    spl10_18 | ~spl10_19 | ~spl10_9),
% 1.49/0.59    inference(avatar_split_clause,[],[f380,f217,f386,f382])).
% 1.49/0.59  fof(f380,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK3) | v1_tsep_1(sK3,sK3) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f378,f127])).
% 1.49/0.59  fof(f378,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_pre_topc(sK3,sK3) | v1_tsep_1(sK3,sK3) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f322,f219])).
% 1.49/0.59  fof(f322,plain,(
% 1.49/0.59    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f318,f154])).
% 1.49/0.59  fof(f318,plain,(
% 1.49/0.59    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | ~v3_pre_topc(u1_struct_0(X3),sK3) | v1_tsep_1(X3,sK3)) )),
% 1.49/0.59    inference(resolution,[],[f116,f123])).
% 1.49/0.59  fof(f372,plain,(
% 1.49/0.59    spl10_17),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f371])).
% 1.49/0.59  fof(f371,plain,(
% 1.49/0.59    $false | spl10_17),
% 1.49/0.59    inference(subsumption_resolution,[],[f370,f155])).
% 1.49/0.59  fof(f370,plain,(
% 1.49/0.59    ~v2_pre_topc(sK2) | spl10_17),
% 1.49/0.59    inference(subsumption_resolution,[],[f369,f124])).
% 1.49/0.59  fof(f369,plain,(
% 1.49/0.59    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl10_17),
% 1.49/0.59    inference(resolution,[],[f368,f86])).
% 1.49/0.59  fof(f368,plain,(
% 1.49/0.59    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | spl10_17),
% 1.49/0.59    inference(subsumption_resolution,[],[f367,f115])).
% 1.49/0.59  fof(f367,plain,(
% 1.49/0.59    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl10_17),
% 1.49/0.59    inference(resolution,[],[f365,f299])).
% 1.49/0.59  fof(f299,plain,(
% 1.49/0.59    ( ! [X2] : (v3_pre_topc(X2,sK2) | ~r2_hidden(X2,u1_pre_topc(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.49/0.59    inference(resolution,[],[f92,f124])).
% 1.49/0.59  fof(f365,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK2) | spl10_17),
% 1.49/0.59    inference(avatar_component_clause,[],[f363])).
% 1.49/0.59  fof(f366,plain,(
% 1.49/0.59    spl10_16 | ~spl10_17 | ~spl10_9),
% 1.49/0.59    inference(avatar_split_clause,[],[f357,f217,f363,f359])).
% 1.49/0.59  fof(f357,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK2) | v1_tsep_1(sK3,sK2) | ~spl10_9),
% 1.49/0.59    inference(subsumption_resolution,[],[f355,f210])).
% 1.49/0.59  fof(f355,plain,(
% 1.49/0.59    ~v3_pre_topc(u1_struct_0(sK2),sK2) | ~m1_pre_topc(sK3,sK2) | v1_tsep_1(sK3,sK2) | ~spl10_9),
% 1.49/0.59    inference(superposition,[],[f321,f219])).
% 1.49/0.59  fof(f267,plain,(
% 1.49/0.59    spl10_10),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f266])).
% 1.49/0.59  fof(f266,plain,(
% 1.49/0.59    $false | spl10_10),
% 1.49/0.59    inference(subsumption_resolution,[],[f264,f223])).
% 1.49/0.59  fof(f223,plain,(
% 1.49/0.59    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | spl10_10),
% 1.49/0.59    inference(avatar_component_clause,[],[f221])).
% 1.49/0.59  fof(f221,plain,(
% 1.49/0.59    spl10_10 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.49/0.59  fof(f264,plain,(
% 1.49/0.59    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.49/0.59    inference(resolution,[],[f259,f129])).
% 1.49/0.59  fof(f259,plain,(
% 1.49/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | r1_tarski(u1_struct_0(X2),u1_struct_0(sK3))) )),
% 1.49/0.59    inference(resolution,[],[f255,f168])).
% 1.49/0.59  fof(f168,plain,(
% 1.49/0.59    ( ! [X3] : (~m1_pre_topc(X3,sK3) | r1_tarski(u1_struct_0(X3),u1_struct_0(sK3))) )),
% 1.49/0.59    inference(resolution,[],[f90,f123])).
% 1.49/0.59  fof(f90,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f29])).
% 1.49/0.59  fof(f29,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f16])).
% 1.49/0.59  fof(f16,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.49/0.59  fof(f224,plain,(
% 1.49/0.59    spl10_9 | ~spl10_10),
% 1.49/0.59    inference(avatar_split_clause,[],[f215,f221,f217])).
% 1.49/0.59  fof(f215,plain,(
% 1.49/0.59    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.49/0.59    inference(resolution,[],[f212,f106])).
% 1.49/0.59  fof(f106,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f212,plain,(
% 1.49/0.59    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.49/0.59    inference(resolution,[],[f210,f167])).
% 1.49/0.59  fof(f167,plain,(
% 1.49/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))) )),
% 1.49/0.59    inference(resolution,[],[f90,f124])).
% 1.49/0.59  % SZS output end Proof for theBenchmark
% 1.49/0.59  % (25484)------------------------------
% 1.49/0.59  % (25484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (25484)Termination reason: Refutation
% 1.49/0.59  
% 1.49/0.59  % (25484)Memory used [KB]: 11257
% 1.49/0.59  % (25484)Time elapsed: 0.128 s
% 1.49/0.59  % (25484)------------------------------
% 1.49/0.59  % (25484)------------------------------
% 1.49/0.60  % (25461)Success in time 0.234 s
%------------------------------------------------------------------------------
