%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 293 expanded)
%              Number of leaves         :   37 ( 136 expanded)
%              Depth                    :    9
%              Number of atoms          :  502 ( 976 expanded)
%              Number of equality atoms :   59 ( 115 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f69,f73,f77,f81,f85,f89,f93,f110,f133,f142,f148,f164,f176,f180,f201,f277,f306,f308,f310,f312,f314,f316,f337])).

fof(f337,plain,
    ( ~ spl4_1
    | spl4_24
    | ~ spl4_31 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl4_1
    | spl4_24
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f175,f322])).

fof(f322,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f59,f285])).

fof(f285,plain,
    ( ! [X1] :
        ( k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ l1_orders_2(X1) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_31
  <=> ! [X1] :
        ( k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f59,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f175,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_24
  <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f316,plain,
    ( ~ spl4_5
    | ~ spl4_27
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_27
    | spl4_32 ),
    inference(subsumption_resolution,[],[f205,f289])).

fof(f289,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl4_32
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f205,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(superposition,[],[f76,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f76,plain,
    ( ! [X0] : v1_yellow_1(sK3(X0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_5
  <=> ! [X0] : v1_yellow_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f314,plain,
    ( ~ spl4_7
    | ~ spl4_27
    | spl4_33 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_27
    | spl4_33 ),
    inference(subsumption_resolution,[],[f203,f293])).

fof(f293,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl4_33
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f203,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(superposition,[],[f84,f200])).

fof(f84,plain,
    ( ! [X0] : v1_partfun1(sK3(X0),X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_7
  <=> ! [X0] : v1_partfun1(sK3(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f312,plain,
    ( ~ spl4_4
    | ~ spl4_27
    | spl4_34 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_27
    | spl4_34 ),
    inference(subsumption_resolution,[],[f206,f297])).

fof(f297,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl4_34
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f206,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(superposition,[],[f72,f200])).

fof(f72,plain,
    ( ! [X0] : v1_funct_1(sK3(X0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_4
  <=> ! [X0] : v1_funct_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f310,plain,
    ( ~ spl4_6
    | ~ spl4_27
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_27
    | spl4_35 ),
    inference(subsumption_resolution,[],[f204,f301])).

fof(f301,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_35
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f204,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(superposition,[],[f80,f200])).

fof(f80,plain,
    ( ! [X0] : v4_relat_1(sK3(X0),X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_6
  <=> ! [X0] : v4_relat_1(sK3(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f308,plain,
    ( ~ spl4_3
    | ~ spl4_27
    | spl4_36 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_27
    | spl4_36 ),
    inference(subsumption_resolution,[],[f207,f305])).

fof(f305,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl4_36
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f207,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(superposition,[],[f68,f200])).

fof(f68,plain,
    ( ! [X0] : v1_relat_1(sK3(X0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_3
  <=> ! [X0] : v1_relat_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f306,plain,
    ( spl4_31
    | ~ spl4_32
    | ~ spl4_33
    | ~ spl4_34
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f282,f275,f178,f108,f303,f299,f295,f291,f287,f284])).

fof(f108,plain,
    ( spl4_13
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f178,plain,
    ( spl4_25
  <=> ! [X1,X0] : ~ r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f275,plain,
    ( spl4_30
  <=> ! [X1] :
        ( k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f282,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ l1_orders_2(X1) )
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f281,f182])).

fof(f182,plain,
    ( ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f179,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f179,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f281,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f280,f182])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f279,f182])).

fof(f279,plain,
    ( ! [X1] :
        ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f278,f182])).

fof(f278,plain,
    ( ! [X1] :
        ( ~ v1_yellow_1(k1_xboole_0)
        | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f276,f182])).

fof(f276,plain,
    ( ! [X1] :
        ( k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl4_30
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f155,f146,f140,f131,f83,f79,f75,f71,f67,f275])).

fof(f131,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f140,plain,
    ( spl4_20
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f146,plain,
    ( spl4_21
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f155,plain,
    ( ! [X1] :
        ( k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f150,f154])).

fof(f154,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f149,f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f68,f72,f80,f84,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f140])).

fof(f149,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f68,f76,f72,f80,f84,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f146])).

fof(f150,plain,
    ( ! [X1] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(superposition,[],[f147,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f201,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f143,f140,f83,f79,f71,f67,f198])).

fof(f180,plain,
    ( spl4_25
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f106,f91,f87,f178])).

fof(f87,plain,
    ( spl4_8
  <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f91,plain,
    ( spl4_9
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f106,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f88,f92])).

fof(f92,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f88,plain,
    ( ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f176,plain,
    ( ~ spl4_24
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f171,f162,f140,f83,f79,f75,f71,f67,f173])).

fof(f162,plain,
    ( spl4_23
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f171,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f165,f143])).

fof(f165,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f68,f76,f72,f80,f84,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( spl4_23
    | spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f153,f146,f62,f162])).

fof(f62,plain,
    ( spl4_2
  <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f153,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | spl4_2
    | ~ spl4_21 ),
    inference(superposition,[],[f64,f147])).

fof(f64,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f148,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f38,f146])).

fof(f38,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f142,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f39,f140])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(f133,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f51,f131])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f110,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f42,f108])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f93,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f54,f87])).

fof(f54,plain,(
    ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f36,f48])).

% (7904)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (7893)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (7890)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (7892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f36,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f85,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    ! [X0] : v1_partfun1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_yellow_1(sK3(X0))
      & v1_partfun1(sK3(X0),X0)
      & v1_funct_1(sK3(X0))
      & v4_relat_1(sK3(X0),X0)
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_yellow_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v1_yellow_1(sK3(X0))
        & v1_partfun1(sK3(X0),X0)
        & v1_funct_1(sK3(X0))
        & v4_relat_1(sK3(X0),X0)
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f81,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    ! [X0] : v4_relat_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f47,f75])).

fof(f47,plain,(
    ! [X0] : v1_yellow_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f71])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f67])).

% (7905)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f43,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f60,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (7899)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.45  % (7894)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (7894)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f338,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f60,f65,f69,f73,f77,f81,f85,f89,f93,f110,f133,f142,f148,f164,f176,f180,f201,f277,f306,f308,f310,f312,f314,f316,f337])).
% 0.22/0.46  fof(f337,plain,(
% 0.22/0.46    ~spl4_1 | spl4_24 | ~spl4_31),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f336])).
% 0.22/0.46  fof(f336,plain,(
% 0.22/0.46    $false | (~spl4_1 | spl4_24 | ~spl4_31)),
% 0.22/0.46    inference(subsumption_resolution,[],[f175,f322])).
% 0.22/0.46  fof(f322,plain,(
% 0.22/0.46    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_31)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f59,f285])).
% 0.22/0.46  fof(f285,plain,(
% 0.22/0.46    ( ! [X1] : (k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~l1_orders_2(X1)) ) | ~spl4_31),
% 0.22/0.46    inference(avatar_component_clause,[],[f284])).
% 0.22/0.46  fof(f284,plain,(
% 0.22/0.46    spl4_31 <=> ! [X1] : (k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~l1_orders_2(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    l1_orders_2(sK0) | ~spl4_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl4_1 <=> l1_orders_2(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,k1_xboole_0) | spl4_24),
% 0.22/0.46    inference(avatar_component_clause,[],[f173])).
% 0.22/0.46  fof(f173,plain,(
% 0.22/0.46    spl4_24 <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.46  fof(f316,plain,(
% 0.22/0.46    ~spl4_5 | ~spl4_27 | spl4_32),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.46  fof(f315,plain,(
% 0.22/0.46    $false | (~spl4_5 | ~spl4_27 | spl4_32)),
% 0.22/0.46    inference(subsumption_resolution,[],[f205,f289])).
% 0.22/0.46  fof(f289,plain,(
% 0.22/0.46    ~v1_yellow_1(k1_xboole_0) | spl4_32),
% 0.22/0.46    inference(avatar_component_clause,[],[f287])).
% 0.22/0.46  fof(f287,plain,(
% 0.22/0.46    spl4_32 <=> v1_yellow_1(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.46  fof(f205,plain,(
% 0.22/0.46    v1_yellow_1(k1_xboole_0) | (~spl4_5 | ~spl4_27)),
% 0.22/0.46    inference(superposition,[],[f76,f200])).
% 0.22/0.46  fof(f200,plain,(
% 0.22/0.46    k1_xboole_0 = sK3(k1_xboole_0) | ~spl4_27),
% 0.22/0.46    inference(avatar_component_clause,[],[f198])).
% 0.22/0.46  fof(f198,plain,(
% 0.22/0.46    spl4_27 <=> k1_xboole_0 = sK3(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ( ! [X0] : (v1_yellow_1(sK3(X0))) ) | ~spl4_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl4_5 <=> ! [X0] : v1_yellow_1(sK3(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.46  fof(f314,plain,(
% 0.22/0.46    ~spl4_7 | ~spl4_27 | spl4_33),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f313])).
% 0.22/0.46  fof(f313,plain,(
% 0.22/0.46    $false | (~spl4_7 | ~spl4_27 | spl4_33)),
% 0.22/0.46    inference(subsumption_resolution,[],[f203,f293])).
% 0.22/0.46  fof(f293,plain,(
% 0.22/0.46    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl4_33),
% 0.22/0.46    inference(avatar_component_clause,[],[f291])).
% 0.22/0.46  fof(f291,plain,(
% 0.22/0.46    spl4_33 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.46  fof(f203,plain,(
% 0.22/0.46    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_7 | ~spl4_27)),
% 0.22/0.46    inference(superposition,[],[f84,f200])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ( ! [X0] : (v1_partfun1(sK3(X0),X0)) ) | ~spl4_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f83])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl4_7 <=> ! [X0] : v1_partfun1(sK3(X0),X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.46  fof(f312,plain,(
% 0.22/0.46    ~spl4_4 | ~spl4_27 | spl4_34),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f311])).
% 0.22/0.46  fof(f311,plain,(
% 0.22/0.46    $false | (~spl4_4 | ~spl4_27 | spl4_34)),
% 0.22/0.46    inference(subsumption_resolution,[],[f206,f297])).
% 0.22/0.46  fof(f297,plain,(
% 0.22/0.46    ~v1_funct_1(k1_xboole_0) | spl4_34),
% 0.22/0.46    inference(avatar_component_clause,[],[f295])).
% 0.22/0.46  fof(f295,plain,(
% 0.22/0.46    spl4_34 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.46  fof(f206,plain,(
% 0.22/0.46    v1_funct_1(k1_xboole_0) | (~spl4_4 | ~spl4_27)),
% 0.22/0.46    inference(superposition,[],[f72,f200])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    ( ! [X0] : (v1_funct_1(sK3(X0))) ) | ~spl4_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl4_4 <=> ! [X0] : v1_funct_1(sK3(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.46  fof(f310,plain,(
% 0.22/0.46    ~spl4_6 | ~spl4_27 | spl4_35),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.46  fof(f309,plain,(
% 0.22/0.46    $false | (~spl4_6 | ~spl4_27 | spl4_35)),
% 0.22/0.46    inference(subsumption_resolution,[],[f204,f301])).
% 0.22/0.46  fof(f301,plain,(
% 0.22/0.46    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | spl4_35),
% 0.22/0.46    inference(avatar_component_clause,[],[f299])).
% 0.22/0.46  fof(f299,plain,(
% 0.22/0.46    spl4_35 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.46  fof(f204,plain,(
% 0.22/0.46    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_27)),
% 0.22/0.46    inference(superposition,[],[f80,f200])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    ( ! [X0] : (v4_relat_1(sK3(X0),X0)) ) | ~spl4_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl4_6 <=> ! [X0] : v4_relat_1(sK3(X0),X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.46  fof(f308,plain,(
% 0.22/0.46    ~spl4_3 | ~spl4_27 | spl4_36),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f307])).
% 0.22/0.46  fof(f307,plain,(
% 0.22/0.46    $false | (~spl4_3 | ~spl4_27 | spl4_36)),
% 0.22/0.46    inference(subsumption_resolution,[],[f207,f305])).
% 0.22/0.46  fof(f305,plain,(
% 0.22/0.46    ~v1_relat_1(k1_xboole_0) | spl4_36),
% 0.22/0.46    inference(avatar_component_clause,[],[f303])).
% 0.22/0.46  fof(f303,plain,(
% 0.22/0.46    spl4_36 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.46  fof(f207,plain,(
% 0.22/0.46    v1_relat_1(k1_xboole_0) | (~spl4_3 | ~spl4_27)),
% 0.22/0.46    inference(superposition,[],[f68,f200])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(sK3(X0))) ) | ~spl4_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl4_3 <=> ! [X0] : v1_relat_1(sK3(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.46  fof(f306,plain,(
% 0.22/0.46    spl4_31 | ~spl4_32 | ~spl4_33 | ~spl4_34 | ~spl4_35 | ~spl4_36 | ~spl4_13 | ~spl4_25 | ~spl4_30),
% 0.22/0.46    inference(avatar_split_clause,[],[f282,f275,f178,f108,f303,f299,f295,f291,f287,f284])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    spl4_13 <=> ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.46  fof(f178,plain,(
% 0.22/0.46    spl4_25 <=> ! [X1,X0] : ~r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.46  fof(f275,plain,(
% 0.22/0.46    spl4_30 <=> ! [X1] : (k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.46  fof(f282,plain,(
% 0.22/0.46    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~l1_orders_2(X1)) ) | (~spl4_13 | ~spl4_25 | ~spl4_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f281,f182])).
% 0.22/0.46  fof(f182,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) ) | (~spl4_13 | ~spl4_25)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f179,f109])).
% 0.22/0.46  fof(f109,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_13),
% 0.22/0.46    inference(avatar_component_clause,[],[f108])).
% 0.22/0.46  fof(f179,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1))) ) | ~spl4_25),
% 0.22/0.46    inference(avatar_component_clause,[],[f178])).
% 0.22/0.46  fof(f281,plain,(
% 0.22/0.46    ( ! [X1] : (~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_13 | ~spl4_25 | ~spl4_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f280,f182])).
% 0.22/0.46  fof(f280,plain,(
% 0.22/0.46    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_13 | ~spl4_25 | ~spl4_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f279,f182])).
% 0.22/0.46  fof(f279,plain,(
% 0.22/0.46    ( ! [X1] : (~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_13 | ~spl4_25 | ~spl4_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f278,f182])).
% 0.22/0.46  fof(f278,plain,(
% 0.22/0.46    ( ! [X1] : (~v1_yellow_1(k1_xboole_0) | k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_13 | ~spl4_25 | ~spl4_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f276,f182])).
% 0.22/0.46  fof(f276,plain,(
% 0.22/0.46    ( ! [X1] : (k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | ~spl4_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f275])).
% 0.22/0.46  fof(f277,plain,(
% 0.22/0.46    spl4_30 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_18 | ~spl4_20 | ~spl4_21),
% 0.22/0.46    inference(avatar_split_clause,[],[f155,f146,f140,f131,f83,f79,f75,f71,f67,f275])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    spl4_18 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    spl4_20 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    spl4_21 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.46  fof(f155,plain,(
% 0.22/0.46    ( ! [X1] : (k6_yellow_1(k1_xboole_0,X1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_18 | ~spl4_20 | ~spl4_21)),
% 0.22/0.46    inference(forward_demodulation,[],[f150,f154])).
% 0.22/0.46  fof(f154,plain,(
% 0.22/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_20 | ~spl4_21)),
% 0.22/0.46    inference(forward_demodulation,[],[f149,f143])).
% 0.22/0.46  fof(f143,plain,(
% 0.22/0.46    k1_xboole_0 = sK3(k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_20)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f68,f72,f80,f84,f141])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_20),
% 0.22/0.46    inference(avatar_component_clause,[],[f140])).
% 0.22/0.46  fof(f149,plain,(
% 0.22/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK3(k1_xboole_0)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_21)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f68,f76,f72,f80,f84,f147])).
% 0.22/0.46  fof(f147,plain,(
% 0.22/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_21),
% 0.22/0.46    inference(avatar_component_clause,[],[f146])).
% 0.22/0.46  fof(f150,plain,(
% 0.22/0.46    ( ! [X1] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl4_18 | ~spl4_21)),
% 0.22/0.46    inference(superposition,[],[f147,f132])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl4_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f131])).
% 0.22/0.46  fof(f201,plain,(
% 0.22/0.46    spl4_27 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_20),
% 0.22/0.46    inference(avatar_split_clause,[],[f143,f140,f83,f79,f71,f67,f198])).
% 0.22/0.46  fof(f180,plain,(
% 0.22/0.46    spl4_25 | ~spl4_8 | ~spl4_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f106,f91,f87,f178])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl4_8 <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.46  fof(f91,plain,(
% 0.22/0.46    spl4_9 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.46  fof(f106,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k7_funcop_1(k1_xboole_0,X1))) ) | (~spl4_8 | ~spl4_9)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f88,f92])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl4_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f91])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) ) | ~spl4_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f87])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    ~spl4_24 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_20 | ~spl4_23),
% 0.22/0.46    inference(avatar_split_clause,[],[f171,f162,f140,f83,f79,f75,f71,f67,f173])).
% 0.22/0.46  fof(f162,plain,(
% 0.22/0.46    spl4_23 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.46  fof(f171,plain,(
% 0.22/0.46    k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_20 | ~spl4_23)),
% 0.22/0.46    inference(forward_demodulation,[],[f165,f143])).
% 0.22/0.46  fof(f165,plain,(
% 0.22/0.46    k6_yellow_1(k1_xboole_0,sK0) != k5_yellow_1(k1_xboole_0,sK3(k1_xboole_0)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_23)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f68,f76,f72,f80,f84,f163])).
% 0.22/0.46  fof(f163,plain,(
% 0.22/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_23),
% 0.22/0.46    inference(avatar_component_clause,[],[f162])).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    spl4_23 | spl4_2 | ~spl4_21),
% 0.22/0.46    inference(avatar_split_clause,[],[f153,f146,f62,f162])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    spl4_2 <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.46  fof(f153,plain,(
% 0.22/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | (spl4_2 | ~spl4_21)),
% 0.22/0.46    inference(superposition,[],[f64,f147])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) | spl4_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f62])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    spl4_21),
% 0.22/0.46    inference(avatar_split_clause,[],[f38,f146])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.22/0.46  fof(f142,plain,(
% 0.22/0.46    spl4_20),
% 0.22/0.46    inference(avatar_split_clause,[],[f39,f140])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    spl4_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f51,f131])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.22/0.46  fof(f110,plain,(
% 0.22/0.46    spl4_13),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f108])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl4_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f40,f91])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(rectify,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(nnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    spl4_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f54,f87])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f36,f48])).
% 0.22/0.47  % (7904)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (7893)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (7890)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (7892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f46,f83])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (v1_partfun1(sK3(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0] : (v1_yellow_1(sK3(X0)) & v1_partfun1(sK3(X0),X0) & v1_funct_1(sK3(X0)) & v4_relat_1(sK3(X0),X0) & v1_relat_1(sK3(X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_yellow_1(sK3(X0)) & v1_partfun1(sK3(X0),X0) & v1_funct_1(sK3(X0)) & v4_relat_1(sK3(X0),X0) & v1_relat_1(sK3(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f79])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (v4_relat_1(sK3(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f75])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (v1_yellow_1(sK3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f71])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f67])).
% 0.22/0.48  % (7905)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f62])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f14])).
% 0.22/0.48  fof(f14,conjecture,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f57])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7894)------------------------------
% 0.22/0.48  % (7894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7894)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7894)Memory used [KB]: 6268
% 0.22/0.48  % (7894)Time elapsed: 0.044 s
% 0.22/0.48  % (7894)------------------------------
% 0.22/0.48  % (7894)------------------------------
% 0.22/0.48  % (7888)Success in time 0.118 s
%------------------------------------------------------------------------------
