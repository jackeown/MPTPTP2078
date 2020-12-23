%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 215 expanded)
%              Number of leaves         :   38 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 612 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f63,f67,f71,f76,f80,f84,f88,f96,f110,f120,f124,f130,f134,f155,f178,f222,f230,f269,f422,f424])).

fof(f424,plain,
    ( ~ spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | spl3_30
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | spl3_30
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f274,f421])).

fof(f421,plain,
    ( ! [X0,X1] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl3_43
  <=> ! [X1,X0] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f274,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | spl3_30 ),
    inference(forward_demodulation,[],[f273,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f273,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | spl3_30 ),
    inference(forward_demodulation,[],[f272,f109])).

fof(f109,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_13
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f272,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_14
    | ~ spl3_15
    | spl3_30 ),
    inference(forward_demodulation,[],[f270,f119])).

fof(f119,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_14
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f270,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | ~ spl3_15
    | spl3_30 ),
    inference(unit_resulting_resolution,[],[f268,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f268,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl3_30
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f422,plain,
    ( spl3_43
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f111,f94,f65,f420])).

fof(f65,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( ! [X0,X1] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f66,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f66,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f269,plain,
    ( ~ spl3_30
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_24
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f257,f228,f219,f153,f132,f86,f73,f56,f51,f266])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( spl3_7
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f132,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f153,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f219,plain,
    ( spl3_24
  <=> r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f228,plain,
    ( spl3_26
  <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f257,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_24
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f256,f232])).

fof(f232,plain,
    ( ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f229,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f229,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f256,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f172,f255])).

fof(f255,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f221,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f221,plain,
    ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f172,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f171,f156])).

fof(f156,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f53,f133])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f171,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f170,f156])).

fof(f170,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f169,f157])).

fof(f157,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f58,f133])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f169,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_7
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f167,f165])).

fof(f165,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f53,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f167,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7
    | ~ spl3_18 ),
    inference(superposition,[],[f75,f154])).

fof(f75,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f230,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f179,f176,f69,f51,f46,f228])).

fof(f46,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f176,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f179,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f48,f70,f53,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f70,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f48,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f222,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f186,f127,f94,f61,f219])).

fof(f61,plain,
    ( spl3_4
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f127,plain,
    ( spl3_16
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f186,plain,
    ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f184,f62])).

fof(f62,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f184,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f129,f95])).

fof(f129,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f178,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f32,f176])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f155,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f43,f153])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f134,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f40,f132])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f130,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f82,f51,f127])).

fof(f82,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f53,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f124,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f120,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f38,f118])).

fof(f38,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f110,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f37,f108])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f39,f94])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f88,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f76,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f67,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (12566)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (12552)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (12553)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (12555)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (12563)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (12554)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (12558)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (12568)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (12559)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (12560)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (12556)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (12564)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (12561)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (12556)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f49,f54,f59,f63,f67,f71,f76,f80,f84,f88,f96,f110,f120,f124,f130,f134,f155,f178,f222,f230,f269,f422,f424])).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    ~spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | spl3_30 | ~spl3_43),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f423])).
% 0.22/0.50  fof(f423,plain,(
% 0.22/0.50    $false | (~spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | spl3_30 | ~spl3_43)),
% 0.22/0.50    inference(subsumption_resolution,[],[f274,f421])).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))) ) | ~spl3_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f420])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    spl3_43 <=> ! [X1,X0] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | (~spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | spl3_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f273,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | (~spl3_13 | ~spl3_14 | ~spl3_15 | spl3_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f272,f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl3_13 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (~spl3_14 | ~spl3_15 | spl3_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f270,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl3_14 <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | (~spl3_15 | spl3_30)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f268,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl3_15 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f266])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    spl3_30 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f422,plain,(
% 0.22/0.50    spl3_43 | ~spl3_5 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f111,f94,f65,f420])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl3_12 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))) ) | (~spl3_5 | ~spl3_12)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f66,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ~spl3_30 | ~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_10 | ~spl3_17 | ~spl3_18 | ~spl3_24 | ~spl3_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f257,f228,f219,f153,f132,f86,f73,f56,f51,f266])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl3_7 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl3_17 <=> ! [X1,X0] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl3_18 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl3_24 <=> r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl3_26 <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_10 | ~spl3_17 | ~spl3_18 | ~spl3_24 | ~spl3_26)),
% 0.22/0.50    inference(forward_demodulation,[],[f256,f232])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ( ! [X0] : (k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) ) | (~spl3_17 | ~spl3_26)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f229,f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f132])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f228])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_10 | ~spl3_17 | ~spl3_18 | ~spl3_24)),
% 0.22/0.50    inference(subsumption_resolution,[],[f172,f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_10 | ~spl3_24)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f221,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) | ~spl3_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f219])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_17 | ~spl3_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f171,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | (~spl3_2 | ~spl3_17)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f53,f133])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_17 | ~spl3_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f156])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | spl3_7 | ~spl3_17 | ~spl3_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f169,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | (~spl3_3 | ~spl3_17)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f58,f133])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_7 | ~spl3_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f167,f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl3_2 | ~spl3_18)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f53,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_7 | ~spl3_18)),
% 0.22/0.50    inference(superposition,[],[f75,f154])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    spl3_26 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f179,f176,f69,f51,f46,f228])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_1 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl3_19 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f48,f70,f53,f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) ) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f176])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl3_24 | ~spl3_4 | ~spl3_12 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f186,f127,f94,f61,f219])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl3_4 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl3_16 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) | (~spl3_4 | ~spl3_12 | ~spl3_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f184,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_12 | ~spl3_16)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f129,f95])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f176])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f153])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f132])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl3_16 | ~spl3_2 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f100,f82,f51,f127])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f53,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl3_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f122])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f118])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f108])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f94])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f86])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f82])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f78])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f73])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f14])).
% 0.22/0.50  fof(f14,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f69])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f65])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f61])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f56])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f51])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f46])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (12556)------------------------------
% 0.22/0.50  % (12556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12556)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (12556)Memory used [KB]: 6396
% 0.22/0.50  % (12556)Time elapsed: 0.076 s
% 0.22/0.50  % (12556)------------------------------
% 0.22/0.50  % (12556)------------------------------
% 0.22/0.50  % (12550)Success in time 0.137 s
%------------------------------------------------------------------------------
