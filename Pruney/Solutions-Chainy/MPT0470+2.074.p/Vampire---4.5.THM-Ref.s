%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 228 expanded)
%              Number of leaves         :   39 ( 110 expanded)
%              Depth                    :    7
%              Number of atoms          :  458 ( 700 expanded)
%              Number of equality atoms :   74 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f72,f76,f81,f86,f90,f94,f98,f104,f108,f113,f140,f154,f172,f176,f256,f272,f277,f396,f400,f415,f886,f927,f1355,f1397])).

fof(f1397,plain,
    ( ~ spl1_1
    | spl1_3
    | ~ spl1_5
    | ~ spl1_31
    | ~ spl1_76 ),
    inference(avatar_contradiction_clause,[],[f1396])).

fof(f1396,plain,
    ( $false
    | ~ spl1_1
    | spl1_3
    | ~ spl1_5
    | ~ spl1_31
    | ~ spl1_76 ),
    inference(subsumption_resolution,[],[f67,f1356])).

fof(f1356,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_1
    | ~ spl1_5
    | ~ spl1_31
    | ~ spl1_76 ),
    inference(unit_resulting_resolution,[],[f57,f75,f276,f1354])).

fof(f1354,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0)) )
    | ~ spl1_76 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1353,plain,
    ( spl1_76
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_76])])).

fof(f276,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_31 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl1_31
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f75,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl1_3
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f1355,plain,
    ( ~ spl1_13
    | spl1_76
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_30
    | ~ spl1_42 ),
    inference(avatar_split_clause,[],[f426,f413,f270,f96,f92,f83,f78,f1353,f110])).

fof(f110,plain,
    ( spl1_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f78,plain,
    ( spl1_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f83,plain,
    ( spl1_7
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f92,plain,
    ( spl1_9
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f96,plain,
    ( spl1_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f270,plain,
    ( spl1_30
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f413,plain,
    ( spl1_42
  <=> ! [X1,X0] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_30
    | ~ spl1_42 ),
    inference(forward_demodulation,[],[f425,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f425,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_30
    | ~ spl1_42 ),
    inference(forward_demodulation,[],[f424,f93])).

fof(f93,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f424,plain,
    ( ! [X0] :
        ( k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_30
    | ~ spl1_42 ),
    inference(forward_demodulation,[],[f416,f282])).

fof(f282,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl1_10
    | ~ spl1_30 ),
    inference(unit_resulting_resolution,[],[f271,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f271,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f416,plain,
    ( ! [X0] :
        ( k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_6
    | ~ spl1_42 ),
    inference(superposition,[],[f414,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_42 ),
    inference(avatar_component_clause,[],[f413])).

fof(f927,plain,
    ( ~ spl1_1
    | spl1_4
    | ~ spl1_5
    | ~ spl1_40
    | ~ spl1_68 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | ~ spl1_1
    | spl1_4
    | ~ spl1_5
    | ~ spl1_40
    | ~ spl1_68 ),
    inference(subsumption_resolution,[],[f71,f887])).

fof(f887,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_5
    | ~ spl1_40
    | ~ spl1_68 ),
    inference(unit_resulting_resolution,[],[f57,f75,f395,f885])).

fof(f885,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ r1_tarski(k1_xboole_0,k2_relat_1(X0)) )
    | ~ spl1_68 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl1_68
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_68])])).

fof(f395,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_40 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl1_40
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).

fof(f71,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl1_4
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f886,plain,
    ( ~ spl1_13
    | spl1_68
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_29
    | ~ spl1_41 ),
    inference(avatar_split_clause,[],[f411,f398,f254,f96,f92,f83,f78,f884,f110])).

fof(f254,plain,
    ( spl1_29
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).

fof(f398,plain,
    ( spl1_41
  <=> ! [X1,X0] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_29
    | ~ spl1_41 ),
    inference(forward_demodulation,[],[f410,f80])).

fof(f410,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_29
    | ~ spl1_41 ),
    inference(forward_demodulation,[],[f409,f93])).

fof(f409,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k3_xboole_0(k5_relat_1(X0,k1_xboole_0),k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_29
    | ~ spl1_41 ),
    inference(forward_demodulation,[],[f403,f261])).

fof(f261,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_29 ),
    inference(unit_resulting_resolution,[],[f255,f97])).

fof(f255,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl1_29 ),
    inference(avatar_component_clause,[],[f254])).

fof(f403,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k3_xboole_0(k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_7
    | ~ spl1_41 ),
    inference(superposition,[],[f399,f85])).

fof(f399,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_41 ),
    inference(avatar_component_clause,[],[f398])).

fof(f415,plain,
    ( spl1_42
    | ~ spl1_19
    | ~ spl1_23 ),
    inference(avatar_split_clause,[],[f178,f174,f152,f413])).

fof(f152,plain,
    ( spl1_19
  <=> ! [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f174,plain,
    ( spl1_23
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_19
    | ~ spl1_23 ),
    inference(superposition,[],[f153,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f174])).

% (24088)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f153,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f400,plain,
    ( spl1_41
    | ~ spl1_19
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f177,f170,f152,f398])).

fof(f170,plain,
    ( spl1_22
  <=> ! [X1,X0] :
        ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_19
    | ~ spl1_22 ),
    inference(superposition,[],[f153,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f396,plain,
    ( spl1_40
    | ~ spl1_1
    | ~ spl1_13
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f246,f138,f110,f55,f393])).

fof(f138,plain,
    ( spl1_16
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f246,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_13
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f57,f112,f139])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f112,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f277,plain,
    ( spl1_31
    | ~ spl1_1
    | ~ spl1_13
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f243,f138,f110,f55,f274])).

fof(f243,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_13
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f57,f112,f139])).

fof(f272,plain,
    ( spl1_30
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f127,f106,f60,f270])).

fof(f60,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f106,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f127,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f62,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f62,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f256,plain,
    ( spl1_29
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f125,f102,f60,f254])).

fof(f102,plain,
    ( spl1_11
  <=> ! [X1,X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f125,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(unit_resulting_resolution,[],[f62,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f176,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f45,f174])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f172,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f44,f170])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f154,plain,(
    spl1_19 ),
    inference(avatar_split_clause,[],[f43,f152])).

fof(f43,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f140,plain,(
    spl1_16 ),
    inference(avatar_split_clause,[],[f50,f138])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f113,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f99,f88,f60,f110])).

fof(f88,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f99,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f62,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f108,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f49,f106])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f104,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f98,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f42,f96])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f94,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f40,f92])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f90,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f86,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f81,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,
    ( ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f35,f69,f65])).

fof(f35,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f63,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f36,f60])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 13:15:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.47  % (24081)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (24092)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (24092)Refutation not found, incomplete strategy% (24092)------------------------------
% 0.22/0.48  % (24092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24092)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (24092)Memory used [KB]: 10618
% 0.22/0.48  % (24092)Time elapsed: 0.042 s
% 0.22/0.48  % (24092)------------------------------
% 0.22/0.48  % (24092)------------------------------
% 0.22/0.48  % (24086)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (24091)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (24082)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (24083)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (24094)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (24085)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (24089)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (24093)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (24090)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (24084)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.53  % (24087)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (24086)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1404,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f58,f63,f72,f76,f81,f86,f90,f94,f98,f104,f108,f113,f140,f154,f172,f176,f256,f272,f277,f396,f400,f415,f886,f927,f1355,f1397])).
% 0.22/0.53  fof(f1397,plain,(
% 0.22/0.53    ~spl1_1 | spl1_3 | ~spl1_5 | ~spl1_31 | ~spl1_76),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1396])).
% 0.22/0.53  fof(f1396,plain,(
% 0.22/0.53    $false | (~spl1_1 | spl1_3 | ~spl1_5 | ~spl1_31 | ~spl1_76)),
% 0.22/0.53    inference(subsumption_resolution,[],[f67,f1356])).
% 0.22/0.53  fof(f1356,plain,(
% 0.22/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_1 | ~spl1_5 | ~spl1_31 | ~spl1_76)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f57,f75,f276,f1354])).
% 0.22/0.53  fof(f1354,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0))) ) | ~spl1_76),
% 0.22/0.53    inference(avatar_component_clause,[],[f1353])).
% 0.22/0.53  fof(f1353,plain,(
% 0.22/0.53    spl1_76 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_76])])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    spl1_31 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl1_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl1_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl1_1 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl1_3 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.53  fof(f1355,plain,(
% 0.22/0.53    ~spl1_13 | spl1_76 | ~spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_10 | ~spl1_30 | ~spl1_42),
% 0.22/0.53    inference(avatar_split_clause,[],[f426,f413,f270,f96,f92,f83,f78,f1353,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl1_13 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl1_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl1_7 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl1_9 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl1_10 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    spl1_30 <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    spl1_42 <=> ! [X1,X0] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_10 | ~spl1_30 | ~spl1_42)),
% 0.22/0.53    inference(forward_demodulation,[],[f425,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_6 | ~spl1_9 | ~spl1_10 | ~spl1_30 | ~spl1_42)),
% 0.22/0.53    inference(forward_demodulation,[],[f424,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f424,plain,(
% 0.22/0.53    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_6 | ~spl1_10 | ~spl1_30 | ~spl1_42)),
% 0.22/0.53    inference(forward_demodulation,[],[f416,f282])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | (~spl1_10 | ~spl1_30)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f271,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl1_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl1_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f270])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_6 | ~spl1_42)),
% 0.22/0.53    inference(superposition,[],[f414,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_42),
% 0.22/0.53    inference(avatar_component_clause,[],[f413])).
% 0.22/0.53  fof(f927,plain,(
% 0.22/0.53    ~spl1_1 | spl1_4 | ~spl1_5 | ~spl1_40 | ~spl1_68),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f926])).
% 0.22/0.53  fof(f926,plain,(
% 0.22/0.53    $false | (~spl1_1 | spl1_4 | ~spl1_5 | ~spl1_40 | ~spl1_68)),
% 0.22/0.53    inference(subsumption_resolution,[],[f71,f887])).
% 0.22/0.53  fof(f887,plain,(
% 0.22/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_1 | ~spl1_5 | ~spl1_40 | ~spl1_68)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f57,f75,f395,f885])).
% 0.22/0.53  fof(f885,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(X0))) ) | ~spl1_68),
% 0.22/0.53    inference(avatar_component_clause,[],[f884])).
% 0.22/0.53  fof(f884,plain,(
% 0.22/0.53    spl1_68 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_68])])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_40),
% 0.22/0.53    inference(avatar_component_clause,[],[f393])).
% 0.22/0.53  fof(f393,plain,(
% 0.22/0.53    spl1_40 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl1_4 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.53  fof(f886,plain,(
% 0.22/0.53    ~spl1_13 | spl1_68 | ~spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_10 | ~spl1_29 | ~spl1_41),
% 0.22/0.53    inference(avatar_split_clause,[],[f411,f398,f254,f96,f92,f83,f78,f884,f110])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    spl1_29 <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    spl1_41 <=> ! [X1,X0] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).
% 0.22/0.53  fof(f411,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_10 | ~spl1_29 | ~spl1_41)),
% 0.22/0.53    inference(forward_demodulation,[],[f410,f80])).
% 0.22/0.53  fof(f410,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_7 | ~spl1_9 | ~spl1_10 | ~spl1_29 | ~spl1_41)),
% 0.22/0.53    inference(forward_demodulation,[],[f409,f93])).
% 0.22/0.53  fof(f409,plain,(
% 0.22/0.53    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k3_xboole_0(k5_relat_1(X0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_7 | ~spl1_10 | ~spl1_29 | ~spl1_41)),
% 0.22/0.53    inference(forward_demodulation,[],[f403,f261])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | (~spl1_10 | ~spl1_29)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f255,f97])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl1_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f254])).
% 0.22/0.53  fof(f403,plain,(
% 0.22/0.53    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k3_xboole_0(k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_7 | ~spl1_41)),
% 0.22/0.53    inference(superposition,[],[f399,f85])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) ) | ~spl1_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f398])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    spl1_42 | ~spl1_19 | ~spl1_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f178,f174,f152,f413])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl1_19 <=> ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl1_23 <=> ! [X1,X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl1_19 | ~spl1_23)),
% 0.22/0.53    inference(superposition,[],[f153,f175])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f174])).
% 0.22/0.54  % (24088)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) ) | ~spl1_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f152])).
% 0.22/0.54  fof(f400,plain,(
% 0.22/0.54    spl1_41 | ~spl1_19 | ~spl1_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f177,f170,f152,f398])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl1_22 <=> ! [X1,X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) ) | (~spl1_19 | ~spl1_22)),
% 0.22/0.54    inference(superposition,[],[f153,f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f170])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    spl1_40 | ~spl1_1 | ~spl1_13 | ~spl1_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f246,f138,f110,f55,f393])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl1_16 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_13 | ~spl1_16)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f57,f112,f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f138])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0) | ~spl1_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f110])).
% 0.22/0.54  fof(f277,plain,(
% 0.22/0.54    spl1_31 | ~spl1_1 | ~spl1_13 | ~spl1_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f243,f138,f110,f55,f274])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_13 | ~spl1_16)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f57,f112,f139])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    spl1_30 | ~spl1_2 | ~spl1_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f127,f106,f60,f270])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl1_12 <=> ! [X1,X0] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) ) | (~spl1_2 | ~spl1_12)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) ) | ~spl1_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f106])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f60])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    spl1_29 | ~spl1_2 | ~spl1_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f125,f102,f60,f254])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    spl1_11 <=> ! [X1,X0] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | (~spl1_2 | ~spl1_11)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) ) | ~spl1_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f102])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    spl1_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f174])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl1_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f170])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    spl1_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f152])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    spl1_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f50,f138])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl1_13 | ~spl1_2 | ~spl1_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f99,f88,f60,f110])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl1_8 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_8)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl1_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f88])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    spl1_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f106])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl1_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f102])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl1_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f96])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl1_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f92])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl1_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f88])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl1_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f83])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl1_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f37,f78])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl1_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f74])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~spl1_3 | ~spl1_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f35,f69,f65])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f18])).
% 0.22/0.54  fof(f18,conjecture,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl1_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f60])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    spl1_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f34,f55])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    v1_relat_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24086)------------------------------
% 0.22/0.54  % (24086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24086)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24086)Memory used [KB]: 6908
% 0.22/0.54  % (24086)Time elapsed: 0.112 s
% 0.22/0.54  % (24086)------------------------------
% 0.22/0.54  % (24086)------------------------------
% 0.22/0.54  % (24096)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.54  % (24080)Success in time 0.176 s
%------------------------------------------------------------------------------
