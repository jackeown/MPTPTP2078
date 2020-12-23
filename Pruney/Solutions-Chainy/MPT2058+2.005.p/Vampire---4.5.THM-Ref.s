%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  179 (1071 expanded)
%              Number of leaves         :   22 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  858 (6574 expanded)
%              Number of equality atoms :   17 ( 136 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f167,f181,f221,f233,f244,f267,f275,f280,f284])).

fof(f284,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f282,f103])).

fof(f103,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_1
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f282,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl3_2
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f281,f92])).

fof(f92,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f37,f91])).

fof(f91,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (20850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f281,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl3_2
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(resolution,[],[f276,f106])).

fof(f106,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_2
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f276,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f258,f262])).

fof(f262,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_18
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f258,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f257,f134])).

fof(f134,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f133,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f41,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

% (20852)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f132,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f131,f40])).

fof(f40,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f130,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X8] :
      ( ~ v1_subset_1(X8,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(X8)
      | ~ v2_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X8)) = X8 ) ),
    inference(subsumption_resolution,[],[f75,f84])).

fof(f75,plain,(
    ! [X8] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(X8)
      | ~ v1_subset_1(X8,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X8)) = X8 ) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f256,f91])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f255,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f253,f45])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(resolution,[],[f246,f43])).

fof(f246,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
        | ~ r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) )
    | spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f245,f216])).

fof(f216,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_16
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f245,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
        | ~ r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) )
    | spl3_8
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f169,f212])).

fof(f212,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl3_15
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f169,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
        | ~ r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) )
    | spl3_8 ),
    inference(resolution,[],[f162,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f162,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_8
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f280,plain,
    ( ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f278,f107])).

fof(f107,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f278,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f277,f92])).

% (20853)Termination reason: Refutation not found, incomplete strategy
fof(f277,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f266,f109])).

fof(f109,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f36,f107])).

% (20853)Memory used [KB]: 10746
% (20853)Time elapsed: 0.118 s
fof(f36,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

% (20853)------------------------------
% (20853)------------------------------
fof(f266,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f265])).

% (20848)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f265,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f275,plain,
    ( ~ spl3_9
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl3_9
    | spl3_18 ),
    inference(subsumption_resolution,[],[f273,f165])).

fof(f165,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_9
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f273,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f272,f42])).

fof(f272,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f271,f41])).

fof(f271,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f270,f40])).

fof(f270,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f269,f38])).

fof(f269,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f268,f157])).

fof(f157,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f156,f92])).

fof(f156,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f155,f91])).

fof(f155,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f154,f91])).

fof(f154,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f153,f43])).

fof(f153,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f45])).

fof(f152,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f44])).

fof(f149,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f145,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
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
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_connsp_2(sK0,sK2),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f116,f92])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f93,plain,(
    ! [X9] :
      ( r2_hidden(X9,k1_connsp_2(sK0,X9))
      | ~ m1_subset_1(X9,k2_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f83,f91])).

fof(f83,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,k1_connsp_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,k1_connsp_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f76,f44])).

fof(f76,plain,(
    ! [X9] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,k1_connsp_2(sK0,X9)) ) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_connsp_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
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
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f268,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(resolution,[],[f263,f94])).

fof(f94,plain,(
    ! [X14,X15] :
      ( l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0)
      | v1_xboole_0(X14)
      | v1_xboole_0(X15)
      | ~ v2_waybel_0(X15,k3_yellow_1(X14))
      | ~ v13_waybel_0(X15,k3_yellow_1(X14))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14))))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f85,f91])).

fof(f85,plain,(
    ! [X14,X15] :
      ( v1_xboole_0(X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X15)
      | ~ v2_waybel_0(X15,k3_yellow_1(X14))
      | ~ v13_waybel_0(X15,k3_yellow_1(X14))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14))))
      | l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0) ) ),
    inference(subsumption_resolution,[],[f79,f84])).

fof(f79,plain,(
    ! [X14,X15] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X15)
      | ~ v2_waybel_0(X15,k3_yellow_1(X14))
      | ~ v13_waybel_0(X15,k3_yellow_1(X14))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14))))
      | l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0) ) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

% (20855)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f263,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f261])).

fof(f267,plain,
    ( ~ spl3_18
    | spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f252,f219,f265,f261])).

fof(f219,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) )
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f251,f91])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) )
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f250,f134])).

fof(f250,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) )
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f249,f45])).

fof(f249,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f247,f44])).

fof(f247,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_17 ),
    inference(resolution,[],[f220,f43])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f244,plain,
    ( ~ spl3_9
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_9
    | spl3_16 ),
    inference(subsumption_resolution,[],[f242,f165])).

fof(f242,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_16 ),
    inference(forward_demodulation,[],[f241,f91])).

fof(f241,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(subsumption_resolution,[],[f240,f43])).

fof(f240,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f239,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f238,f41])).

fof(f238,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f237,f40])).

fof(f237,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f236,f38])).

fof(f236,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f235,f157])).

fof(f235,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f234,f84])).

fof(f234,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(resolution,[],[f217,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f217,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f233,plain,
    ( ~ spl3_9
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl3_9
    | spl3_15 ),
    inference(subsumption_resolution,[],[f231,f165])).

fof(f231,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_15 ),
    inference(forward_demodulation,[],[f230,f91])).

fof(f230,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(subsumption_resolution,[],[f229,f43])).

fof(f229,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f228,f42])).

fof(f228,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f227,f41])).

fof(f227,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f226,f40])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f225,f39])).

fof(f225,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f224,f38])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f223,f157])).

fof(f223,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f222,f84])).

fof(f222,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl3_15 ),
    inference(resolution,[],[f213,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f213,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f221,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_17
    | spl3_8 ),
    inference(avatar_split_clause,[],[f168,f160,f219,f215,f211])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | spl3_8 ),
    inference(resolution,[],[f162,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f181,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f179,f70])).

fof(f70,plain,(
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

fof(f179,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f166,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f166,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f167,plain,
    ( ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f158,f164,f160])).

fof(f158,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f148,f157])).

fof(f148,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f147,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f146,f40])).

fof(f146,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f129,f41])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(sK1,k3_yellow_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1)) ) ),
    inference(resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X11)
      | v1_xboole_0(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X11,k3_yellow_1(X10))
      | ~ v13_waybel_0(X11,k3_yellow_1(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10))))
      | ~ v2_struct_0(k3_yellow19(sK0,X10,X11)) ) ),
    inference(backward_demodulation,[],[f87,f91])).

fof(f87,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X11)
      | ~ v2_waybel_0(X11,k3_yellow_1(X10))
      | ~ v13_waybel_0(X11,k3_yellow_1(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10))))
      | ~ v2_struct_0(k3_yellow19(sK0,X10,X11)) ) ),
    inference(subsumption_resolution,[],[f77,f84])).

fof(f77,plain,(
    ! [X10,X11] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X11)
      | ~ v2_waybel_0(X11,k3_yellow_1(X10))
      | ~ v13_waybel_0(X11,k3_yellow_1(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10))))
      | ~ v2_struct_0(k3_yellow19(sK0,X10,X11)) ) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f105,f101])).

fof(f35,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n002.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:29:21 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.44  % (20845)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.46  % (20845)Refutation not found, incomplete strategy% (20845)------------------------------
% 0.19/0.46  % (20845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (20845)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (20845)Memory used [KB]: 1918
% 0.19/0.46  % (20845)Time elapsed: 0.096 s
% 0.19/0.46  % (20845)------------------------------
% 0.19/0.46  % (20845)------------------------------
% 0.19/0.48  % (20869)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.48  % (20861)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.49  % (20842)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.49  % (20844)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.49  % (20842)Refutation not found, incomplete strategy% (20842)------------------------------
% 0.19/0.49  % (20842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (20842)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (20842)Memory used [KB]: 1791
% 0.19/0.49  % (20842)Time elapsed: 0.092 s
% 0.19/0.49  % (20842)------------------------------
% 0.19/0.49  % (20842)------------------------------
% 0.19/0.49  % (20861)Refutation not found, incomplete strategy% (20861)------------------------------
% 0.19/0.49  % (20861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (20861)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (20861)Memory used [KB]: 1791
% 0.19/0.49  % (20861)Time elapsed: 0.112 s
% 0.19/0.49  % (20861)------------------------------
% 0.19/0.49  % (20861)------------------------------
% 0.19/0.49  % (20853)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.49  % (20864)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (20865)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.50  % (20869)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (20853)Refutation not found, incomplete strategy% (20853)------------------------------
% 0.19/0.50  % (20853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f285,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f108,f167,f181,f221,f233,f244,f267,f275,f280,f284])).
% 0.19/0.50  fof(f284,plain,(
% 0.19/0.50    ~spl3_1 | spl3_2 | spl3_8 | ~spl3_15 | ~spl3_16 | ~spl3_18),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f283])).
% 0.19/0.50  fof(f283,plain,(
% 0.19/0.50    $false | (~spl3_1 | spl3_2 | spl3_8 | ~spl3_15 | ~spl3_16 | ~spl3_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f282,f103])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl3_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f101])).
% 0.19/0.50  fof(f101,plain,(
% 0.19/0.50    spl3_1 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.50  fof(f282,plain,(
% 0.19/0.50    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | (spl3_2 | spl3_8 | ~spl3_15 | ~spl3_16 | ~spl3_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f281,f92])).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.19/0.50    inference(backward_demodulation,[],[f37,f91])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f84,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    l1_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f45,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  % (20850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  fof(f15,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.19/0.50    inference(negated_conjecture,[],[f14])).
% 0.19/0.50  fof(f14,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f281,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | (spl3_2 | spl3_8 | ~spl3_15 | ~spl3_16 | ~spl3_18)),
% 0.19/0.50    inference(resolution,[],[f276,f106])).
% 0.19/0.50  fof(f106,plain,(
% 0.19/0.50    ~r1_waybel_7(sK0,sK1,sK2) | spl3_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f105])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    spl3_2 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.50  fof(f276,plain,(
% 0.19/0.50    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16 | ~spl3_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f258,f262])).
% 0.19/0.50  fof(f262,plain,(
% 0.19/0.50    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl3_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f261])).
% 0.19/0.50  fof(f261,plain,(
% 0.19/0.50    spl3_18 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.50  fof(f258,plain,(
% 0.19/0.50    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(forward_demodulation,[],[f257,f134])).
% 0.19/0.50  fof(f134,plain,(
% 0.19/0.50    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f133,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f132,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  % (20852)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f131,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f131,plain,(
% 0.19/0.50    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f130,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ~v1_xboole_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f130,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(resolution,[],[f88,f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    ( ! [X8] : (~v1_subset_1(X8,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(X8) | ~v2_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X8)) = X8) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f75,f84])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    ( ! [X8] : (~l1_struct_0(sK0) | v1_xboole_0(X8) | ~v1_subset_1(X8,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X8,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X8)) = X8) )),
% 0.19/0.50    inference(resolution,[],[f43,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,axiom,(
% 0.19/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f257,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(forward_demodulation,[],[f256,f91])).
% 0.19/0.50  fof(f256,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(subsumption_resolution,[],[f255,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f255,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(subsumption_resolution,[],[f253,f45])).
% 0.19/0.50  fof(f253,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(resolution,[],[f246,f43])).
% 0.19/0.50  fof(f246,plain,(
% 0.19/0.50    ( ! [X2,X3] : (v2_struct_0(X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | ~r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)) ) | (spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.19/0.50    inference(subsumption_resolution,[],[f245,f216])).
% 0.19/0.50  fof(f216,plain,(
% 0.19/0.50    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_16),
% 0.19/0.50    inference(avatar_component_clause,[],[f215])).
% 0.19/0.50  fof(f215,plain,(
% 0.19/0.50    spl3_16 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.50  fof(f245,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | ~r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)) ) | (spl3_8 | ~spl3_15)),
% 0.19/0.50    inference(subsumption_resolution,[],[f169,f212])).
% 0.19/0.50  fof(f212,plain,(
% 0.19/0.50    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_15),
% 0.19/0.50    inference(avatar_component_clause,[],[f211])).
% 0.19/0.50  fof(f211,plain,(
% 0.19/0.50    spl3_15 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | ~r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)) ) | spl3_8),
% 0.19/0.50    inference(resolution,[],[f162,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 0.19/0.50  fof(f162,plain,(
% 0.19/0.50    ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f160])).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    spl3_8 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.50  fof(f280,plain,(
% 0.19/0.50    ~spl3_2 | ~spl3_19),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f279])).
% 0.19/0.50  fof(f279,plain,(
% 0.19/0.50    $false | (~spl3_2 | ~spl3_19)),
% 0.19/0.50    inference(subsumption_resolution,[],[f278,f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    r1_waybel_7(sK0,sK1,sK2) | ~spl3_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f105])).
% 0.19/0.50  fof(f278,plain,(
% 0.19/0.50    ~r1_waybel_7(sK0,sK1,sK2) | (~spl3_2 | ~spl3_19)),
% 0.19/0.50    inference(subsumption_resolution,[],[f277,f92])).
% 0.19/0.50  % (20853)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  fof(f277,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,sK2) | (~spl3_2 | ~spl3_19)),
% 0.19/0.50    inference(resolution,[],[f266,f109])).
% 0.19/0.50  
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f36,f107])).
% 0.19/0.50  % (20853)Memory used [KB]: 10746
% 0.19/0.50  % (20853)Time elapsed: 0.118 s
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  % (20853)------------------------------
% 0.19/0.50  % (20853)------------------------------
% 0.19/0.50  fof(f266,plain,(
% 0.19/0.50    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0)) ) | ~spl3_19),
% 0.19/0.50    inference(avatar_component_clause,[],[f265])).
% 0.19/0.50  % (20848)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  fof(f265,plain,(
% 0.19/0.50    spl3_19 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,sK1,X0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.50  fof(f275,plain,(
% 0.19/0.50    ~spl3_9 | spl3_18),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f274])).
% 0.19/0.50  fof(f274,plain,(
% 0.19/0.50    $false | (~spl3_9 | spl3_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f273,f165])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f164])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    spl3_9 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.50  fof(f273,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(subsumption_resolution,[],[f272,f42])).
% 0.19/0.50  fof(f272,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(subsumption_resolution,[],[f271,f41])).
% 0.19/0.50  fof(f271,plain,(
% 0.19/0.50    ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(subsumption_resolution,[],[f270,f40])).
% 0.19/0.50  fof(f270,plain,(
% 0.19/0.50    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(subsumption_resolution,[],[f269,f38])).
% 0.19/0.50  fof(f269,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(subsumption_resolution,[],[f268,f157])).
% 0.19/0.50  fof(f157,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f156,f92])).
% 0.19/0.50  fof(f156,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.50    inference(forward_demodulation,[],[f155,f91])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.50    inference(forward_demodulation,[],[f154,f91])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f153,f43])).
% 0.19/0.50  fof(f153,plain,(
% 0.19/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f152,f45])).
% 0.19/0.50  fof(f152,plain,(
% 0.19/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f149,f44])).
% 0.19/0.50  fof(f149,plain,(
% 0.19/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f145,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(k1_connsp_2(sK0,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f116,f92])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) )),
% 0.19/0.50    inference(resolution,[],[f93,f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    ( ! [X9] : (r2_hidden(X9,k1_connsp_2(sK0,X9)) | ~m1_subset_1(X9,k2_struct_0(sK0))) )),
% 0.19/0.50    inference(backward_demodulation,[],[f83,f91])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    ( ! [X9] : (~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,k1_connsp_2(sK0,X9))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f82,f45])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X9] : (~l1_pre_topc(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,k1_connsp_2(sK0,X9))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f76,f44])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    ( ! [X9] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,k1_connsp_2(sK0,X9))) )),
% 0.19/0.50    inference(resolution,[],[f43,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k1_connsp_2(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.19/0.50  fof(f268,plain,(
% 0.19/0.50    v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.19/0.50    inference(resolution,[],[f263,f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ( ! [X14,X15] : (l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0) | v1_xboole_0(X14) | v1_xboole_0(X15) | ~v2_waybel_0(X15,k3_yellow_1(X14)) | ~v13_waybel_0(X15,k3_yellow_1(X14)) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) | ~m1_subset_1(X14,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.19/0.50    inference(backward_demodulation,[],[f85,f91])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    ( ! [X14,X15] : (v1_xboole_0(X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X15) | ~v2_waybel_0(X15,k3_yellow_1(X14)) | ~v13_waybel_0(X15,k3_yellow_1(X14)) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) | l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f79,f84])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X14,X15] : (~l1_struct_0(sK0) | v1_xboole_0(X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X15) | ~v2_waybel_0(X15,k3_yellow_1(X14)) | ~v13_waybel_0(X15,k3_yellow_1(X14)) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) | l1_waybel_0(k3_yellow19(sK0,X14,X15),sK0)) )),
% 0.19/0.50    inference(resolution,[],[f43,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f30])).
% 0.19/0.50  % (20855)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.19/0.50  fof(f263,plain,(
% 0.19/0.50    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | spl3_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f261])).
% 0.19/0.50  fof(f267,plain,(
% 0.19/0.50    ~spl3_18 | spl3_19 | ~spl3_17),
% 0.19/0.50    inference(avatar_split_clause,[],[f252,f219,f265,f261])).
% 0.19/0.50  fof(f219,plain,(
% 0.19/0.50    spl3_17 <=> ! [X1,X0] : (~v2_pre_topc(X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.50  fof(f252,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)) ) | ~spl3_17),
% 0.19/0.50    inference(forward_demodulation,[],[f251,f91])).
% 0.19/0.50  fof(f251,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)) ) | ~spl3_17),
% 0.19/0.50    inference(forward_demodulation,[],[f250,f134])).
% 0.19/0.50  fof(f250,plain,(
% 0.19/0.50    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)) ) | ~spl3_17),
% 0.19/0.50    inference(subsumption_resolution,[],[f249,f45])).
% 0.19/0.50  fof(f249,plain,(
% 0.19/0.50    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_17),
% 0.19/0.50    inference(subsumption_resolution,[],[f247,f44])).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_17),
% 0.19/0.50    inference(resolution,[],[f220,f43])).
% 0.19/0.50  fof(f220,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl3_17),
% 0.19/0.50    inference(avatar_component_clause,[],[f219])).
% 0.19/0.50  fof(f244,plain,(
% 0.19/0.50    ~spl3_9 | spl3_16),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f243])).
% 0.19/0.50  fof(f243,plain,(
% 0.19/0.50    $false | (~spl3_9 | spl3_16)),
% 0.19/0.50    inference(subsumption_resolution,[],[f242,f165])).
% 0.19/0.50  fof(f242,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_16),
% 0.19/0.50    inference(forward_demodulation,[],[f241,f91])).
% 0.19/0.50  fof(f241,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f240,f43])).
% 0.19/0.50  fof(f240,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f239,f42])).
% 0.19/0.50  fof(f239,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f238,f41])).
% 0.19/0.50  fof(f238,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f237,f40])).
% 0.19/0.50  fof(f237,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f236,f38])).
% 0.19/0.50  fof(f236,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f235,f157])).
% 0.19/0.50  fof(f235,plain,(
% 0.19/0.50    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(subsumption_resolution,[],[f234,f84])).
% 0.19/0.50  fof(f234,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_16),
% 0.19/0.50    inference(resolution,[],[f217,f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.19/0.50  fof(f217,plain,(
% 0.19/0.50    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_16),
% 0.19/0.50    inference(avatar_component_clause,[],[f215])).
% 0.19/0.50  fof(f233,plain,(
% 0.19/0.50    ~spl3_9 | spl3_15),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f232])).
% 0.19/0.50  fof(f232,plain,(
% 0.19/0.50    $false | (~spl3_9 | spl3_15)),
% 0.19/0.50    inference(subsumption_resolution,[],[f231,f165])).
% 0.19/0.50  fof(f231,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_15),
% 0.19/0.50    inference(forward_demodulation,[],[f230,f91])).
% 0.19/0.50  fof(f230,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f229,f43])).
% 0.19/0.50  fof(f229,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f228,f42])).
% 0.19/0.50  fof(f228,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f227,f41])).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f226,f40])).
% 0.19/0.50  fof(f226,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f225,f39])).
% 0.19/0.50  fof(f225,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f224,f38])).
% 0.19/0.50  fof(f224,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f223,f157])).
% 0.19/0.50  fof(f223,plain,(
% 0.19/0.50    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f222,f84])).
% 0.19/0.50  fof(f222,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl3_15),
% 0.19/0.50    inference(resolution,[],[f213,f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.19/0.50  fof(f213,plain,(
% 0.19/0.50    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_15),
% 0.19/0.50    inference(avatar_component_clause,[],[f211])).
% 0.19/0.50  fof(f221,plain,(
% 0.19/0.50    ~spl3_15 | ~spl3_16 | spl3_17 | spl3_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f168,f160,f219,f215,f211])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)) ) | spl3_8),
% 0.19/0.50    inference(resolution,[],[f162,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f181,plain,(
% 0.19/0.50    spl3_9),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f180])).
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    $false | spl3_9),
% 0.19/0.50    inference(subsumption_resolution,[],[f179,f70])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.50  fof(f179,plain,(
% 0.19/0.50    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl3_9),
% 0.19/0.50    inference(resolution,[],[f166,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f164])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    ~spl3_8 | ~spl3_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f158,f164,f160])).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f148,f157])).
% 0.19/0.50  fof(f148,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f147,f42])).
% 0.19/0.50  fof(f147,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f146,f40])).
% 0.19/0.50  fof(f146,plain,(
% 0.19/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.50    inference(resolution,[],[f129,f41])).
% 0.19/0.50  fof(f129,plain,(
% 0.19/0.50    ( ! [X0] : (~v13_waybel_0(sK1,k3_yellow_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(X0)) | v1_xboole_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v2_struct_0(k3_yellow19(sK0,X0,sK1))) )),
% 0.19/0.50    inference(resolution,[],[f96,f38])).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    ( ! [X10,X11] : (v1_xboole_0(X11) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_waybel_0(X11,k3_yellow_1(X10)) | ~v13_waybel_0(X11,k3_yellow_1(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10)))) | ~v2_struct_0(k3_yellow19(sK0,X10,X11))) )),
% 0.19/0.50    inference(backward_demodulation,[],[f87,f91])).
% 0.19/0.50  fof(f87,plain,(
% 0.19/0.50    ( ! [X10,X11] : (v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X11) | ~v2_waybel_0(X11,k3_yellow_1(X10)) | ~v13_waybel_0(X11,k3_yellow_1(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10)))) | ~v2_struct_0(k3_yellow19(sK0,X10,X11))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f77,f84])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    ( ! [X10,X11] : (~l1_struct_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X11) | ~v2_waybel_0(X11,k3_yellow_1(X10)) | ~v13_waybel_0(X11,k3_yellow_1(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X10)))) | ~v2_struct_0(k3_yellow19(sK0,X10,X11))) )),
% 0.19/0.50    inference(resolution,[],[f43,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    spl3_1 | spl3_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f35,f105,f101])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (20869)------------------------------
% 0.19/0.50  % (20869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (20869)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (20869)Memory used [KB]: 6396
% 0.19/0.50  % (20869)Time elapsed: 0.124 s
% 0.19/0.50  % (20869)------------------------------
% 0.19/0.50  % (20869)------------------------------
% 0.19/0.50  % (20856)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.51  % (20838)Success in time 0.161 s
%------------------------------------------------------------------------------
