%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 201 expanded)
%              Number of leaves         :   28 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  381 ( 981 expanded)
%              Number of equality atoms :   43 ( 118 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f84,f89,f102,f110,f134,f139,f144,f152,f164,f192,f209,f251])).

fof(f251,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_17
    | ~ spl2_19
    | spl2_21
    | spl2_29 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_17
    | ~ spl2_19
    | spl2_21
    | spl2_29 ),
    inference(subsumption_resolution,[],[f166,f247])).

fof(f247,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl2_17
    | spl2_29 ),
    inference(unit_resulting_resolution,[],[f208,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f208,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl2_29
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f166,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_19
    | spl2_21 ),
    inference(unit_resulting_resolution,[],[f83,f58,f63,f68,f73,f78,f163,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ r2_hidden(X2,X1)
        | ~ v1_xboole_0(X2)
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f163,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl2_21
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_6
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f68,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_5
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f58,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f83,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f209,plain,
    ( ~ spl2_29
    | spl2_9
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f193,f189,f86,f206])).

fof(f86,plain,
    ( spl2_9
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f189,plain,
    ( spl2_26
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f193,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl2_9
    | ~ spl2_26 ),
    inference(superposition,[],[f88,f191])).

fof(f191,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f88,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f192,plain,
    ( spl2_26
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f159,f150,f137,f76,f66,f61,f56,f51,f46,f189])).

fof(f46,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f137,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f150,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f159,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f153,f140])).

fof(f140,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_7
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f78,f138])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f153,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f48,f53,f58,f63,f68,f78,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f150])).

fof(f53,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f48,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f164,plain,
    ( ~ spl2_21
    | spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f121,f108,f100,f51,f46,f161])).

fof(f100,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f108,plain,
    ( spl2_14
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f121,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f116,f111])).

fof(f111,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f53,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f53,f48,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f152,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f41,f150])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f144,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f37,f142])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f139,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f44,f137])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f134,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f43,f132])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f110,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

fof(f102,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f89,plain,(
    ~ spl2_9 ),
    inference(avatar_split_clause,[],[f33,f86])).

fof(f33,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f84,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f79,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (2741)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (2742)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.45  % (2741)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f252,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f84,f89,f102,f110,f134,f139,f144,f152,f164,f192,f209,f251])).
% 0.22/0.45  fof(f251,plain,(
% 0.22/0.45    spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_17 | ~spl2_19 | spl2_21 | spl2_29),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.45  fof(f250,plain,(
% 0.22/0.45    $false | (spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_17 | ~spl2_19 | spl2_21 | spl2_29)),
% 0.22/0.45    inference(subsumption_resolution,[],[f166,f247])).
% 0.22/0.45  fof(f247,plain,(
% 0.22/0.45    r2_hidden(k1_xboole_0,sK1) | (~spl2_17 | spl2_29)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f208,f133])).
% 0.22/0.45  fof(f133,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl2_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f132])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    spl2_17 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.45  fof(f208,plain,(
% 0.22/0.45    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl2_29),
% 0.22/0.45    inference(avatar_component_clause,[],[f206])).
% 0.22/0.45  fof(f206,plain,(
% 0.22/0.45    spl2_29 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    ~r2_hidden(k1_xboole_0,sK1) | (spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_19 | spl2_21)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f83,f58,f63,f68,f73,f78,f163,f143])).
% 0.22/0.45  fof(f143,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | ~spl2_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f142])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    spl2_19 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.45  fof(f163,plain,(
% 0.22/0.45    ~v1_xboole_0(k2_struct_0(sK0)) | spl2_21),
% 0.22/0.45    inference(avatar_component_clause,[],[f161])).
% 0.22/0.45  fof(f161,plain,(
% 0.22/0.45    spl2_21 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl2_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~spl2_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f71])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl2_6 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl2_5 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl2_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ~v1_xboole_0(sK1) | spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl2_3 <=> v1_xboole_0(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0) | ~spl2_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f81])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    spl2_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.45  fof(f209,plain,(
% 0.22/0.45    ~spl2_29 | spl2_9 | ~spl2_26),
% 0.22/0.45    inference(avatar_split_clause,[],[f193,f189,f86,f206])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl2_9 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    spl2_26 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.45  fof(f193,plain,(
% 0.22/0.45    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl2_9 | ~spl2_26)),
% 0.22/0.45    inference(superposition,[],[f88,f191])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl2_26),
% 0.22/0.45    inference(avatar_component_clause,[],[f189])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl2_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f86])).
% 0.22/0.45  fof(f192,plain,(
% 0.22/0.45    spl2_26 | spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_18 | ~spl2_20),
% 0.22/0.45    inference(avatar_split_clause,[],[f159,f150,f137,f76,f66,f61,f56,f51,f46,f189])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl2_1 <=> v2_struct_0(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl2_2 <=> l1_struct_0(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    spl2_18 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    spl2_20 <=> ! [X1,X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_18 | ~spl2_20)),
% 0.22/0.45    inference(forward_demodulation,[],[f153,f140])).
% 0.22/0.45  fof(f140,plain,(
% 0.22/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_7 | ~spl2_18)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f78,f138])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f137])).
% 0.22/0.45  fof(f153,plain,(
% 0.22/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | (spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_20)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f48,f53,f58,f63,f68,f78,f151])).
% 0.22/0.45  fof(f151,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl2_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f150])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    l1_struct_0(sK0) | ~spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f51])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ~v2_struct_0(sK0) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f164,plain,(
% 0.22/0.45    ~spl2_21 | spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f121,f108,f100,f51,f46,f161])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl2_12 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl2_14 <=> ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ~v1_xboole_0(k2_struct_0(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_14)),
% 0.22/0.45    inference(forward_demodulation,[],[f116,f111])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl2_2 | ~spl2_12)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f53,f101])).
% 0.22/0.45  fof(f101,plain,(
% 0.22/0.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl2_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    ~v1_xboole_0(u1_struct_0(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_14)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f53,f48,f109])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl2_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f108])).
% 0.22/0.45  fof(f152,plain,(
% 0.22/0.45    spl2_20),
% 0.22/0.45    inference(avatar_split_clause,[],[f41,f150])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    spl2_19),
% 0.22/0.45    inference(avatar_split_clause,[],[f37,f142])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    spl2_18),
% 0.22/0.45    inference(avatar_split_clause,[],[f44,f137])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    spl2_17),
% 0.22/0.45    inference(avatar_split_clause,[],[f43,f132])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    spl2_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f40,f108])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0] : (((v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) & (v1_xboole_0(u1_struct_0(X0)) | ~v2_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    spl2_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f38,f100])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    ~spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f86])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl2_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f81])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    spl2_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f76])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl2_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f71])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f31,f66])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f61])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ~spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f56])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ~v1_xboole_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f51])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    l1_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ~spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f46])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (2741)------------------------------
% 0.22/0.45  % (2741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (2741)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (2741)Memory used [KB]: 6268
% 0.22/0.45  % (2741)Time elapsed: 0.014 s
% 0.22/0.45  % (2741)------------------------------
% 0.22/0.45  % (2741)------------------------------
% 0.22/0.46  % (2730)Success in time 0.094 s
%------------------------------------------------------------------------------
