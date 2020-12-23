%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 216 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  340 ( 585 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f58,f63,f67,f75,f79,f83,f87,f91,f95,f99,f117,f137,f177,f184,f197,f202,f226,f232,f263,f287,f300])).

fof(f300,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | spl3_27
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | spl3_27
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f236,f295])).

fof(f295,plain,
    ( ! [X6,X5] : r1_tarski(k3_tarski(X6),k3_tarski(k2_xboole_0(X6,X5)))
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(superposition,[],[f262,f286])).

fof(f286,plain,
    ( ! [X2,X3] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_34
  <=> ! [X3,X2] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f262,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_32
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f236,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | spl3_27 ),
    inference(forward_demodulation,[],[f235,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f235,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | spl3_27 ),
    inference(forward_demodulation,[],[f234,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f234,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_9
    | ~ spl3_10
    | spl3_27 ),
    inference(forward_demodulation,[],[f233,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f233,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | ~ spl3_10
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f231,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f231,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_27
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f287,plain,
    ( spl3_34
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f102,f77,f65,f285])).

fof(f102,plain,
    ( ! [X2,X3] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f66])).

fof(f263,plain,
    ( spl3_32
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f112,f85,f56,f261])).

fof(f56,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f112,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f57,f86])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
        | r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f232,plain,
    ( ~ spl3_27
    | ~ spl3_12
    | ~ spl3_23
    | spl3_26 ),
    inference(avatar_split_clause,[],[f227,f223,f200,f89,f229])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f200,plain,
    ( spl3_23
  <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f223,plain,
    ( spl3_26
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f227,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_12
    | ~ spl3_23
    | spl3_26 ),
    inference(forward_demodulation,[],[f225,f204])).

fof(f204,plain,
    ( ! [X0] : k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0))
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f201,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f201,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f225,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f226,plain,
    ( ~ spl3_26
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f178,f174,f134,f115,f89,f60,f51,f46,f223])).

fof(f46,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( spl3_5
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f134,plain,
    ( spl3_16
  <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f174,plain,
    ( spl3_19
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f178,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f150,f176])).

fof(f176,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f150,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f149,f136])).

fof(f136,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f149,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f148,f136])).

fof(f148,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f147,f119])).

fof(f119,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f53,f90])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f147,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_5
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f143,f141])).

fof(f141,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f48,f116])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f143,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5
    | ~ spl3_15 ),
    inference(superposition,[],[f62,f116])).

fof(f62,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f202,plain,
    ( spl3_23
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f198,f195,f182,f200])).

fof(f182,plain,
    ( spl3_20
  <=> ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f195,plain,
    ( spl3_22
  <=> ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f198,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f196,f183])).

fof(f183,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f196,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f138,f97,f46,f195])).

fof(f97,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f138,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f48,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f184,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f141,f115,f46,f182])).

fof(f177,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f132,f93,f89,f46,f174])).

fof(f93,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f132,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f127,f118])).

fof(f118,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f48,f90])).

fof(f127,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f48,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f137,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f118,f89,f46,f134])).

fof(f117,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f37,f115])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f99,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f36,f97])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f95,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f35,f93])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f83,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f63,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f23,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:43:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.43  % (22086)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (22081)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (22081)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f49,f54,f58,f63,f67,f75,f79,f83,f87,f91,f95,f99,f117,f137,f177,f184,f197,f202,f226,f232,f263,f287,f300])).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    ~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_10 | spl3_27 | ~spl3_32 | ~spl3_34),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.46  fof(f299,plain,(
% 0.21/0.46    $false | (~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_10 | spl3_27 | ~spl3_32 | ~spl3_34)),
% 0.21/0.46    inference(subsumption_resolution,[],[f236,f295])).
% 0.21/0.46  fof(f295,plain,(
% 0.21/0.46    ( ! [X6,X5] : (r1_tarski(k3_tarski(X6),k3_tarski(k2_xboole_0(X6,X5)))) ) | (~spl3_32 | ~spl3_34)),
% 0.21/0.46    inference(superposition,[],[f262,f286])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))) ) | ~spl3_34),
% 0.21/0.46    inference(avatar_component_clause,[],[f285])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    spl3_34 <=> ! [X3,X2] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl3_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f261])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    spl3_32 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | (~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_10 | spl3_27)),
% 0.21/0.46    inference(forward_demodulation,[],[f235,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | (~spl3_8 | ~spl3_9 | ~spl3_10 | spl3_27)),
% 0.21/0.46    inference(forward_demodulation,[],[f234,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (~spl3_9 | ~spl3_10 | spl3_27)),
% 0.21/0.46    inference(forward_demodulation,[],[f233,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl3_9 <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | (~spl3_10 | spl3_27)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f231,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | spl3_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f229])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    spl3_27 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.46  fof(f287,plain,(
% 0.21/0.46    spl3_34 | ~spl3_6 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f102,f77,f65,f285])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.46    inference(superposition,[],[f78,f66])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    spl3_32 | ~spl3_4 | ~spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f112,f85,f56,f261])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl3_4 | ~spl3_11)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f57,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    ~spl3_27 | ~spl3_12 | ~spl3_23 | spl3_26),
% 0.21/0.46    inference(avatar_split_clause,[],[f227,f223,f200,f89,f229])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl3_12 <=> ! [X1,X0] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl3_23 <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    spl3_26 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_12 | ~spl3_23 | spl3_26)),
% 0.21/0.46    inference(forward_demodulation,[],[f225,f204])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    ( ! [X0] : (k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0))) ) | (~spl3_12 | ~spl3_23)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f201,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f200])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | spl3_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f223])).
% 0.21/0.46  fof(f226,plain,(
% 0.21/0.46    ~spl3_26 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_15 | ~spl3_16 | ~spl3_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f178,f174,f134,f115,f89,f60,f51,f46,f223])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_5 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl3_15 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    spl3_16 <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    spl3_19 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_15 | ~spl3_16 | ~spl3_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f150,f176])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f174])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_15 | ~spl3_16)),
% 0.21/0.46    inference(forward_demodulation,[],[f149,f136])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f134])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_15 | ~spl3_16)),
% 0.21/0.46    inference(forward_demodulation,[],[f148,f136])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_12 | ~spl3_15)),
% 0.21/0.46    inference(forward_demodulation,[],[f147,f119])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | (~spl3_3 | ~spl3_12)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f53,f90])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_5 | ~spl3_15)),
% 0.21/0.46    inference(forward_demodulation,[],[f143,f141])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl3_2 | ~spl3_15)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_5 | ~spl3_15)),
% 0.21/0.46    inference(superposition,[],[f62,f116])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    spl3_23 | ~spl3_20 | ~spl3_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f198,f195,f182,f200])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    spl3_20 <=> ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    spl3_22 <=> ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_20 | ~spl3_22)),
% 0.21/0.46    inference(forward_demodulation,[],[f196,f183])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f182])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f195])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    spl3_22 | ~spl3_2 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f138,f97,f46,f195])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl3_14 <=> ! [X1,X0,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_2 | ~spl3_14)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    spl3_20 | ~spl3_2 | ~spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f141,f115,f46,f182])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    spl3_19 | ~spl3_2 | ~spl3_12 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f132,f93,f89,f46,f174])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_13 <=> ! [X1,X0] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f127,f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | (~spl3_2 | ~spl3_12)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f90])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_13)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    spl3_16 | ~spl3_2 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f118,f89,f46,f134])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f115])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f97])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f93])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f89])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f85])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f81])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f73])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f65])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f23,f22,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f46])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22081)------------------------------
% 0.21/0.47  % (22081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22081)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22081)Memory used [KB]: 6268
% 0.21/0.47  % (22081)Time elapsed: 0.013 s
% 0.21/0.47  % (22081)------------------------------
% 0.21/0.47  % (22081)------------------------------
% 0.21/0.48  % (22071)Success in time 0.104 s
%------------------------------------------------------------------------------
