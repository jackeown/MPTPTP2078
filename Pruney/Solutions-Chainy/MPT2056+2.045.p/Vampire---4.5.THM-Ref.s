%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 337 expanded)
%              Number of leaves         :   52 ( 161 expanded)
%              Depth                    :    7
%              Number of atoms          :  611 (1400 expanded)
%              Number of equality atoms :   67 ( 164 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f103,f107,f111,f119,f123,f127,f131,f135,f139,f150,f154,f159,f171,f176,f182,f227,f240,f248,f252,f261,f271,f276,f285,f330,f339,f417,f454,f490,f500])).

fof(f500,plain,
    ( ~ spl3_8
    | spl3_44
    | ~ spl3_56
    | ~ spl3_61 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl3_8
    | spl3_44
    | ~ spl3_56
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f418,f496])).

fof(f496,plain,
    ( r1_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | ~ spl3_8
    | ~ spl3_61 ),
    inference(unit_resulting_resolution,[],[f97,f489])).

fof(f489,plain,
    ( ! [X10] :
        ( r1_xboole_0(k1_tarski(X10),sK1)
        | ~ v1_xboole_0(X10) )
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl3_61
  <=> ! [X10] :
        ( ~ v1_xboole_0(X10)
        | r1_xboole_0(k1_tarski(X10),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f97,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f418,plain,
    ( ~ r1_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | spl3_44
    | ~ spl3_56 ),
    inference(unit_resulting_resolution,[],[f329,f416])).

fof(f416,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl3_56
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f329,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl3_44
  <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f490,plain,
    ( spl3_61
    | ~ spl3_46
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f461,f452,f337,f488])).

fof(f337,plain,
    ( spl3_46
  <=> ! [X1] :
        ( ~ v1_xboole_0(sK2(X1,sK1))
        | r1_xboole_0(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f452,plain,
    ( spl3_59
  <=> ! [X1,X0] :
        ( sK2(k1_tarski(X0),X1) = X0
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f461,plain,
    ( ! [X10] :
        ( ~ v1_xboole_0(X10)
        | r1_xboole_0(k1_tarski(X10),sK1) )
    | ~ spl3_46
    | ~ spl3_59 ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,
    ( ! [X10] :
        ( ~ v1_xboole_0(X10)
        | r1_xboole_0(k1_tarski(X10),sK1)
        | r1_xboole_0(k1_tarski(X10),sK1) )
    | ~ spl3_46
    | ~ spl3_59 ),
    inference(superposition,[],[f338,f453])).

fof(f453,plain,
    ( ! [X0,X1] :
        ( sK2(k1_tarski(X0),X1) = X0
        | r1_xboole_0(k1_tarski(X0),X1) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f452])).

fof(f338,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(sK2(X1,sK1))
        | r1_xboole_0(X1,sK1) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f337])).

fof(f454,plain,
    ( spl3_59
    | ~ spl3_15
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f264,f259,f125,f452])).

fof(f125,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f259,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r2_hidden(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( sK2(k1_tarski(X0),X1) = X0
        | r1_xboole_0(k1_tarski(X0),X1) )
    | ~ spl3_15
    | ~ spl3_36 ),
    inference(resolution,[],[f260,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tarski(X1))
        | X0 = X1 )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f259])).

fof(f417,plain,
    ( spl3_56
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f295,f283,f129,f415])).

fof(f129,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f283,plain,
    ( spl3_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(sK2(X1,X2),X0)
        | r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f295,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2) )
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X3,X2)
        | r1_xboole_0(X3,X2) )
    | ~ spl3_16
    | ~ spl3_39 ),
    inference(resolution,[],[f284,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X1,X2),X0)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X2) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f283])).

fof(f339,plain,
    ( spl3_46
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f243,f238,f129,f337])).

fof(f238,plain,
    ( spl3_33
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f243,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(sK2(X1,sK1))
        | r1_xboole_0(X1,sK1) )
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(resolution,[],[f239,f130])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f238])).

fof(f330,plain,
    ( ~ spl3_44
    | spl3_34
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f288,f274,f245,f327])).

fof(f245,plain,
    ( spl3_34
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f274,plain,
    ( spl3_38
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f288,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_34
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f247,f275])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f274])).

fof(f247,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f245])).

fof(f285,plain,
    ( spl3_39
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f166,f152,f125,f283])).

fof(f152,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(sK2(X1,X2),X0)
        | r1_xboole_0(X1,X2) )
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(resolution,[],[f153,f126])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f276,plain,
    ( spl3_38
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f272,f269,f250,f148,f109,f274])).

fof(f109,plain,
    ( spl3_11
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f148,plain,
    ( spl3_20
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f250,plain,
    ( spl3_35
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f269,plain,
    ( spl3_37
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f270,f257])).

fof(f257,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f254,f110])).

fof(f110,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f254,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(superposition,[],[f149,f251])).

fof(f251,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f250])).

fof(f149,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f269])).

fof(f271,plain,
    ( spl3_37
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f165,f148,f137,f269])).

fof(f137,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(superposition,[],[f149,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f261,plain,
    ( spl3_36
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f162,f133,f121,f259])).

fof(f121,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f133,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ r2_hidden(X0,k1_tarski(X1)) )
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(resolution,[],[f134,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f252,plain,
    ( spl3_35
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f163,f137,f105,f250])).

fof(f105,plain,
    ( spl3_10
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f163,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f106,f138])).

fof(f106,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f248,plain,
    ( ~ spl3_34
    | spl3_9
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f228,f224,f100,f245])).

fof(f100,plain,
    ( spl3_9
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f224,plain,
    ( spl3_31
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f228,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_9
    | ~ spl3_31 ),
    inference(superposition,[],[f102,f226])).

fof(f226,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f224])).

fof(f102,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f240,plain,
    ( spl3_22
    | spl3_3
    | ~ spl3_6
    | ~ spl3_4
    | ~ spl3_5
    | spl3_33
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f178,f174,f90,f238,f80,f75,f85,f70,f156])).

fof(f156,plain,
    ( spl3_22
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f70,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_6
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f75,plain,
    ( spl3_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( spl3_5
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f174,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0)
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK1)
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(resolution,[],[f175,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ r2_hidden(X2,X1)
        | ~ v1_xboole_0(X2)
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f174])).

fof(f227,plain,
    ( spl3_31
    | spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f188,f180,f169,f90,f80,f75,f70,f65,f60,f224])).

fof(f60,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( spl3_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f180,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

% (7026)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f188,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f183,f172])).

fof(f172,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f92,f170])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f169])).

fof(f183,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f62,f67,f72,f77,f82,f92,f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f180])).

fof(f82,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f77,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f67,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f182,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f49,f180])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f176,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f47,f174])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f171,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f58,f169])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f159,plain,
    ( ~ spl3_22
    | spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f144,f117,f65,f60,f156])).

fof(f117,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f144,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f62,f67,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f154,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f53,f152])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f150,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f50,f148])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f139,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f55,f137])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f135,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f54,f133])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f131,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f52,f129])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f127,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f51,f125])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f57,f121])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f119,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f111,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f45,f109])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f107,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f44,f105])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f103,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30,f29])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f98,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (7031)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (7021)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (7024)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (7019)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (7032)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (7028)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (7020)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (7027)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (7024)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f501,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f103,f107,f111,f119,f123,f127,f131,f135,f139,f150,f154,f159,f171,f176,f182,f227,f240,f248,f252,f261,f271,f276,f285,f330,f339,f417,f454,f490,f500])).
% 0.20/0.49  fof(f500,plain,(
% 0.20/0.49    ~spl3_8 | spl3_44 | ~spl3_56 | ~spl3_61),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f499])).
% 0.20/0.49  fof(f499,plain,(
% 0.20/0.49    $false | (~spl3_8 | spl3_44 | ~spl3_56 | ~spl3_61)),
% 0.20/0.49    inference(subsumption_resolution,[],[f418,f496])).
% 0.20/0.49  fof(f496,plain,(
% 0.20/0.49    r1_xboole_0(k1_tarski(k1_xboole_0),sK1) | (~spl3_8 | ~spl3_61)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f97,f489])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    ( ! [X10] : (r1_xboole_0(k1_tarski(X10),sK1) | ~v1_xboole_0(X10)) ) | ~spl3_61),
% 0.20/0.49    inference(avatar_component_clause,[],[f488])).
% 0.20/0.49  fof(f488,plain,(
% 0.20/0.49    spl3_61 <=> ! [X10] : (~v1_xboole_0(X10) | r1_xboole_0(k1_tarski(X10),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl3_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f418,plain,(
% 0.20/0.49    ~r1_xboole_0(k1_tarski(k1_xboole_0),sK1) | (spl3_44 | ~spl3_56)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f329,f416])).
% 0.20/0.49  fof(f416,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) ) | ~spl3_56),
% 0.20/0.49    inference(avatar_component_clause,[],[f415])).
% 0.20/0.49  fof(f415,plain,(
% 0.20/0.49    spl3_56 <=> ! [X3,X2] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl3_44),
% 0.20/0.49    inference(avatar_component_clause,[],[f327])).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    spl3_44 <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.49  fof(f490,plain,(
% 0.20/0.49    spl3_61 | ~spl3_46 | ~spl3_59),
% 0.20/0.49    inference(avatar_split_clause,[],[f461,f452,f337,f488])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    spl3_46 <=> ! [X1] : (~v1_xboole_0(sK2(X1,sK1)) | r1_xboole_0(X1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.49  fof(f452,plain,(
% 0.20/0.49    spl3_59 <=> ! [X1,X0] : (sK2(k1_tarski(X0),X1) = X0 | r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.49  fof(f461,plain,(
% 0.20/0.49    ( ! [X10] : (~v1_xboole_0(X10) | r1_xboole_0(k1_tarski(X10),sK1)) ) | (~spl3_46 | ~spl3_59)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f460])).
% 0.20/0.49  fof(f460,plain,(
% 0.20/0.49    ( ! [X10] : (~v1_xboole_0(X10) | r1_xboole_0(k1_tarski(X10),sK1) | r1_xboole_0(k1_tarski(X10),sK1)) ) | (~spl3_46 | ~spl3_59)),
% 0.20/0.49    inference(superposition,[],[f338,f453])).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK2(k1_tarski(X0),X1) = X0 | r1_xboole_0(k1_tarski(X0),X1)) ) | ~spl3_59),
% 0.20/0.49    inference(avatar_component_clause,[],[f452])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_xboole_0(sK2(X1,sK1)) | r1_xboole_0(X1,sK1)) ) | ~spl3_46),
% 0.20/0.49    inference(avatar_component_clause,[],[f337])).
% 0.20/0.49  fof(f454,plain,(
% 0.20/0.49    spl3_59 | ~spl3_15 | ~spl3_36),
% 0.20/0.49    inference(avatar_split_clause,[],[f264,f259,f125,f452])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl3_15 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    spl3_36 <=> ! [X1,X0] : (X0 = X1 | ~r2_hidden(X0,k1_tarski(X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK2(k1_tarski(X0),X1) = X0 | r1_xboole_0(k1_tarski(X0),X1)) ) | (~spl3_15 | ~spl3_36)),
% 0.20/0.49    inference(resolution,[],[f260,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f125])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) ) | ~spl3_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f259])).
% 0.20/0.49  fof(f417,plain,(
% 0.20/0.49    spl3_56 | ~spl3_16 | ~spl3_39),
% 0.20/0.49    inference(avatar_split_clause,[],[f295,f283,f129,f415])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl3_16 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    spl3_39 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(sK2(X1,X2),X0) | r1_xboole_0(X1,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) ) | (~spl3_16 | ~spl3_39)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f294])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) ) | (~spl3_16 | ~spl3_39)),
% 0.20/0.49    inference(resolution,[],[f284,f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) ) | ~spl3_39),
% 0.20/0.49    inference(avatar_component_clause,[],[f283])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    spl3_46 | ~spl3_16 | ~spl3_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f243,f238,f129,f337])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    spl3_33 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_xboole_0(sK2(X1,sK1)) | r1_xboole_0(X1,sK1)) ) | (~spl3_16 | ~spl3_33)),
% 0.20/0.49    inference(resolution,[],[f239,f130])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl3_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f238])).
% 0.20/0.49  fof(f330,plain,(
% 0.20/0.49    ~spl3_44 | spl3_34 | ~spl3_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f288,f274,f245,f327])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    spl3_34 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    spl3_38 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl3_34 | ~spl3_38)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f247,f275])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f274])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl3_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f245])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    spl3_39 | ~spl3_15 | ~spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f166,f152,f125,f283])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl3_21 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(sK2(X1,X2),X0) | r1_xboole_0(X1,X2)) ) | (~spl3_15 | ~spl3_21)),
% 0.20/0.49    inference(resolution,[],[f153,f126])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    spl3_38 | ~spl3_11 | ~spl3_20 | ~spl3_35 | ~spl3_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f272,f269,f250,f148,f109,f274])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl3_11 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl3_20 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    spl3_35 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl3_37 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | (~spl3_11 | ~spl3_20 | ~spl3_35 | ~spl3_37)),
% 0.20/0.49    inference(forward_demodulation,[],[f270,f257])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl3_11 | ~spl3_20 | ~spl3_35)),
% 0.20/0.49    inference(forward_demodulation,[],[f254,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl3_20 | ~spl3_35)),
% 0.20/0.49    inference(superposition,[],[f149,f251])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f250])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f148])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | ~spl3_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f269])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    spl3_37 | ~spl3_18 | ~spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f165,f148,f137,f269])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl3_18 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl3_18 | ~spl3_20)),
% 0.20/0.49    inference(superposition,[],[f149,f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    spl3_36 | ~spl3_14 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f162,f133,f121,f259])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl3_14 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    spl3_17 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(X0,k1_tarski(X1))) ) | (~spl3_14 | ~spl3_17)),
% 0.20/0.49    inference(resolution,[],[f134,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f133])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    spl3_35 | ~spl3_10 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f163,f137,f105,f250])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_10 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_10 | ~spl3_18)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f106,f138])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ~spl3_34 | spl3_9 | ~spl3_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f228,f224,f100,f245])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl3_9 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    spl3_31 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl3_9 | ~spl3_31)),
% 0.20/0.49    inference(superposition,[],[f102,f226])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl3_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f224])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f100])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl3_22 | spl3_3 | ~spl3_6 | ~spl3_4 | ~spl3_5 | spl3_33 | ~spl3_7 | ~spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f178,f174,f90,f238,f80,f75,f85,f70,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl3_22 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl3_3 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_6 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_5 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl3_24 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl3_7 | ~spl3_24)),
% 0.20/0.49    inference(resolution,[],[f175,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f174])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    spl3_31 | spl3_1 | ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_23 | ~spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f188,f180,f169,f90,f80,f75,f70,f65,f60,f224])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_2 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    spl3_23 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl3_25 <=> ! [X1,X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  % (7026)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl3_1 | ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_23 | ~spl3_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f183,f172])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl3_7 | ~spl3_23)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f92,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f169])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | (spl3_1 | ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_25)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f62,f67,f72,f77,f82,f92,f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f60])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f180])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f174])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f169])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    ~spl3_22 | spl3_1 | ~spl3_2 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f117,f65,f60,f156])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_13 <=> ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f62,f67,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f152])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f148])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f55,f137])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f133])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f52,f129])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f125])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f121])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f117])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f109])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f105])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f100])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f14])).
% 0.20/0.49  fof(f14,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f95])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f90])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f85])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f80])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f75])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f70])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f65])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f60])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (7024)------------------------------
% 0.20/0.49  % (7024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7024)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (7024)Memory used [KB]: 6396
% 0.20/0.49  % (7024)Time elapsed: 0.083 s
% 0.20/0.49  % (7024)------------------------------
% 0.20/0.49  % (7024)------------------------------
% 0.20/0.49  % (7025)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (7023)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (7018)Success in time 0.136 s
%------------------------------------------------------------------------------
