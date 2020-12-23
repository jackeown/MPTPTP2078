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
% DateTime   : Thu Dec  3 13:23:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 267 expanded)
%              Number of leaves         :   42 ( 121 expanded)
%              Depth                    :    7
%              Number of atoms          :  492 (1144 expanded)
%              Number of equality atoms :   51 ( 132 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f108,f112,f120,f128,f133,f137,f141,f147,f175,f202,f207,f213,f231,f267,f328,f333,f411,f448,f456])).

fof(f456,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26
    | spl4_29
    | ~ spl4_53
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26
    | spl4_29
    | ~ spl4_53
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f447,f450])).

fof(f450,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26
    | spl4_29
    | ~ spl4_53 ),
    inference(unit_resulting_resolution,[],[f230,f83,f88,f93,f98,f410,f206])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ r2_hidden(X2,X1)
        | ~ v1_xboole_0(X2)
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f410,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl4_53
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f93,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_6
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f88,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_5
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f230,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl4_29
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f447,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl4_57
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f448,plain,
    ( spl4_57
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f337,f326,f139,f106,f445])).

fof(f106,plain,
    ( spl4_9
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f139,plain,
    ( spl4_17
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f326,plain,
    ( spl4_43
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f337,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f335,f107])).

fof(f107,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f335,plain,
    ( ! [X0] : v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))
    | ~ spl4_17
    | ~ spl4_43 ),
    inference(unit_resulting_resolution,[],[f140,f327])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f326])).

fof(f140,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f411,plain,
    ( spl4_53
    | ~ spl4_23
    | spl4_44 ),
    inference(avatar_split_clause,[],[f365,f330,f173,f408])).

fof(f173,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f330,plain,
    ( spl4_44
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f365,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl4_23
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f332,f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f332,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f330])).

fof(f333,plain,
    ( ~ spl4_44
    | spl4_8
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f268,f264,f101,f330])).

fof(f101,plain,
    ( spl4_8
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f264,plain,
    ( spl4_35
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f268,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_8
    | ~ spl4_35 ),
    inference(superposition,[],[f103,f266])).

fof(f266,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f264])).

fof(f103,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

% (8820)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f328,plain,
    ( spl4_43
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f177,f145,f126,f326])).

fof(f126,plain,
    ( spl4_14
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f145,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) )
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(resolution,[],[f146,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f267,plain,
    ( spl4_35
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f220,f211,f200,f96,f86,f81,f76,f71,f66,f264])).

fof(f66,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( spl4_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f76,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f200,plain,
    ( spl4_25
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f211,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f220,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f214,f203])).

fof(f203,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f98,f201])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f214,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f68,f73,f78,f83,f88,f98,f212])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f211])).

fof(f78,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f73,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f68,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f231,plain,
    ( ~ spl4_29
    | spl4_1
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f154,f135,f131,f71,f66,f228])).

fof(f131,plain,
    ( spl4_15
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f135,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f154,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f151,f148])).

fof(f148,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f73,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f151,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f68,f73,f136])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f213,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f53,f211])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
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
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f207,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f64,f205])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f202,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f63,f200])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f175,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f62,f173])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f147,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f60,f145])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f141,plain,
    ( spl4_17
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f129,f118,f110,f139])).

fof(f110,plain,
    ( spl4_10
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f118,plain,
    ( spl4_12
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f129,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f119,f111])).

fof(f111,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f119,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f137,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f52,f135])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f133,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f51,f131])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

% (8828)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f128,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f55,f126])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f56,f118])).

fof(f56,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f112,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f108,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f104,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f99,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:37:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (8821)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8819)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (8817)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (8821)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f457,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f108,f112,f120,f128,f133,f137,f141,f147,f175,f202,f207,f213,f231,f267,f328,f333,f411,f448,f456])).
% 0.22/0.48  fof(f456,plain,(
% 0.22/0.48    ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_26 | spl4_29 | ~spl4_53 | ~spl4_57),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f455])).
% 0.22/0.48  fof(f455,plain,(
% 0.22/0.48    $false | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_26 | spl4_29 | ~spl4_53 | ~spl4_57)),
% 0.22/0.48    inference(subsumption_resolution,[],[f447,f450])).
% 0.22/0.48  fof(f450,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_26 | spl4_29 | ~spl4_53)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f230,f83,f88,f93,f98,f410,f206])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) ) | ~spl4_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f205])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    spl4_26 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.48  fof(f410,plain,(
% 0.22/0.48    r2_hidden(k1_xboole_0,sK1) | ~spl4_53),
% 0.22/0.48    inference(avatar_component_clause,[],[f408])).
% 0.22/0.48  fof(f408,plain,(
% 0.22/0.48    spl4_53 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl4_6 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl4_5 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl4_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f230,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f228])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    spl4_29 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.48  fof(f447,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_57),
% 0.22/0.48    inference(avatar_component_clause,[],[f445])).
% 0.22/0.48  fof(f445,plain,(
% 0.22/0.48    spl4_57 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.22/0.48  fof(f448,plain,(
% 0.22/0.48    spl4_57 | ~spl4_9 | ~spl4_17 | ~spl4_43),
% 0.22/0.48    inference(avatar_split_clause,[],[f337,f326,f139,f106,f445])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl4_9 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    spl4_17 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.48  fof(f326,plain,(
% 0.22/0.48    spl4_43 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.48  fof(f337,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | (~spl4_9 | ~spl4_17 | ~spl4_43)),
% 0.22/0.48    inference(forward_demodulation,[],[f335,f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f106])).
% 0.22/0.48  fof(f335,plain,(
% 0.22/0.48    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))) ) | (~spl4_17 | ~spl4_43)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f140,f327])).
% 0.22/0.48  fof(f327,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl4_43),
% 0.22/0.48    inference(avatar_component_clause,[],[f326])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f139])).
% 0.22/0.48  fof(f411,plain,(
% 0.22/0.48    spl4_53 | ~spl4_23 | spl4_44),
% 0.22/0.48    inference(avatar_split_clause,[],[f365,f330,f173,f408])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    spl4_23 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.48  fof(f330,plain,(
% 0.22/0.48    spl4_44 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.48  fof(f365,plain,(
% 0.22/0.48    r2_hidden(k1_xboole_0,sK1) | (~spl4_23 | spl4_44)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f332,f174])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl4_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f173])).
% 0.22/0.48  fof(f332,plain,(
% 0.22/0.48    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_44),
% 0.22/0.48    inference(avatar_component_clause,[],[f330])).
% 0.22/0.48  fof(f333,plain,(
% 0.22/0.48    ~spl4_44 | spl4_8 | ~spl4_35),
% 0.22/0.48    inference(avatar_split_clause,[],[f268,f264,f101,f330])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl4_8 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    spl4_35 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl4_8 | ~spl4_35)),
% 0.22/0.48    inference(superposition,[],[f103,f266])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl4_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f264])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f101])).
% 0.22/0.48  % (8820)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  fof(f328,plain,(
% 0.22/0.48    spl4_43 | ~spl4_14 | ~spl4_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f177,f145,f126,f326])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl4_14 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl4_18 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) ) | (~spl4_14 | ~spl4_18)),
% 0.22/0.48    inference(resolution,[],[f146,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) ) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl4_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f145])).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    spl4_35 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_25 | ~spl4_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f220,f211,f200,f96,f86,f81,f76,f71,f66,f264])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_2 <=> l1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl4_3 <=> v1_xboole_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    spl4_25 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    spl4_27 <=> ! [X1,X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_25 | ~spl4_27)),
% 0.22/0.48    inference(forward_demodulation,[],[f214,f203])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl4_7 | ~spl4_25)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f98,f201])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f200])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_27)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f68,f73,f78,f83,f88,f98,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f211])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1) | spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    l1_struct_0(sK0) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f231,plain,(
% 0.22/0.48    ~spl4_29 | spl4_1 | ~spl4_2 | ~spl4_15 | ~spl4_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f154,f135,f131,f71,f66,f228])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl4_15 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    spl4_16 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_15 | ~spl4_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f151,f148])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl4_2 | ~spl4_15)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl4_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~v1_xboole_0(u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_16)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f68,f73,f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f135])).
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    spl4_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f53,f211])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    spl4_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f64,f205])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.48    inference(rectify,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl4_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f63,f200])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    spl4_23),
% 0.22/0.48    inference(avatar_split_clause,[],[f62,f173])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl4_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f60,f145])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl4_17 | ~spl4_10 | ~spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f129,f118,f110,f139])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl4_10 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl4_12 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_10 | ~spl4_12)),
% 0.22/0.48    inference(superposition,[],[f119,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    spl4_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f135])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl4_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f51,f131])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.48  % (8828)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl4_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f55,f126])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f56,f118])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f48,f110])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f106])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f46,f101])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f15])).
% 0.22/0.48  fof(f15,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f96])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f42,f91])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f86])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f81])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ~spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f76])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f71])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    l1_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f66])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8821)------------------------------
% 0.22/0.48  % (8821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8821)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8821)Memory used [KB]: 6396
% 0.22/0.48  % (8822)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (8821)Time elapsed: 0.022 s
% 0.22/0.48  % (8821)------------------------------
% 0.22/0.48  % (8821)------------------------------
% 0.22/0.49  % (8824)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (8814)Success in time 0.12 s
%------------------------------------------------------------------------------
