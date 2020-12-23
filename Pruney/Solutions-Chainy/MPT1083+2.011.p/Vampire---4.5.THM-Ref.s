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
% DateTime   : Thu Dec  3 13:08:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 237 expanded)
%              Number of leaves         :   38 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :  503 ( 884 expanded)
%              Number of equality atoms :   87 ( 145 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22036)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f73,f77,f81,f85,f89,f93,f97,f105,f109,f113,f121,f125,f149,f153,f162,f168,f172,f192,f200,f206,f246,f266,f331,f353,f367,f390,f402])).

fof(f402,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_15
    | spl4_57 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_15
    | spl4_57 ),
    inference(subsumption_resolution,[],[f400,f80])).

fof(f80,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_5
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f400,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ spl4_1
    | ~ spl4_15
    | spl4_57 ),
    inference(subsumption_resolution,[],[f398,f64])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f398,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ spl4_15
    | spl4_57 ),
    inference(resolution,[],[f389,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f389,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl4_57 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl4_57
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f390,plain,
    ( ~ spl4_57
    | ~ spl4_1
    | spl4_8
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f382,f365,f147,f91,f63,f388])).

fof(f91,plain,
    ( spl4_8
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f147,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f365,plain,
    ( spl4_54
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f382,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_1
    | spl4_8
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f381,f64])).

fof(f381,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl4_8
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f373,f92])).

fof(f92,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f373,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(superposition,[],[f366,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f147])).

fof(f366,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f365])).

fof(f367,plain,
    ( spl4_54
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f359,f351,f365])).

fof(f351,plain,
    ( spl4_52
  <=> ! [X8] :
        ( sK0 != X8
        | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f359,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0)))
    | ~ spl4_52 ),
    inference(equality_resolution,[],[f352])).

fof(f352,plain,
    ( ! [X8] :
        ( sK0 != X8
        | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8))) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl4_52
    | ~ spl4_1
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f335,f329,f63,f351])).

fof(f329,plain,
    ( spl4_50
  <=> ! [X1,X0] :
        ( sK0 != X0
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f335,plain,
    ( ! [X8] :
        ( sK0 != X8
        | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8))) )
    | ~ spl4_1
    | ~ spl4_50 ),
    inference(resolution,[],[f330,f64])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | sK0 != X0
        | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1)) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl4_50
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f273,f264,f107,f95,f329])).

fof(f95,plain,
    ( spl4_9
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f107,plain,
    ( spl4_12
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f264,plain,
    ( spl4_40
  <=> ! [X1,X0] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1)) )
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f271,f96])).

fof(f96,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(superposition,[],[f265,f108])).

fof(f108,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl4_40
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f249,f244,f190,f103,f87,f264])).

fof(f87,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f103,plain,
    ( spl4_11
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f190,plain,
    ( spl4_30
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f244,plain,
    ( spl4_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X0) != k1_relat_1(X2)
        | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f248,f191])).

fof(f191,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f190])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X1) != k1_relat_1(sK1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f247,f104])).

fof(f104,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X1) != k1_relat_1(sK1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) )
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(resolution,[],[f245,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f245,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X0) != k1_relat_1(X2)
        | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X3) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,
    ( spl4_36
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f178,f170,f111,f244])).

fof(f111,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f170,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k1_relat_1(X0) != k1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f178,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X0) != k1_relat_1(X2)
        | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | ~ v1_relat_1(X3) )
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(resolution,[],[f171,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k1_relat_1(X0) != k1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f170])).

fof(f206,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_24
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_24
    | spl4_29 ),
    inference(unit_resulting_resolution,[],[f76,f72,f84,f88,f188,f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f188,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_29
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f84,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f72,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f200,plain,
    ( ~ spl4_7
    | ~ spl4_11
    | ~ spl4_13
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_13
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f104,f88,f185,f112])).

fof(f185,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_28
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f192,plain,
    ( ~ spl4_28
    | ~ spl4_29
    | spl4_30
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f177,f166,f87,f190,f187,f184])).

fof(f166,plain,
    ( spl4_25
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f177,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(resolution,[],[f167,f88])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f166])).

fof(f172,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f38,f170])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f168,plain,
    ( spl4_25
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f154,f151,f123,f166])).

fof(f123,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f151,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(resolution,[],[f152,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f162,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f41,f160])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f153,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f50,f151])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f149,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f42,f147])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f125,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f51,f123])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f121,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f113,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f109,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f59,f107])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f105,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f103])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f97,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f36,f95])).

fof(f93,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f31,f91])).

fof(f31,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f89,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f33,f83])).

fof(f33,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.50  % (22054)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (22046)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (22042)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (22053)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (22045)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (22050)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (22045)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (22046)Refutation not found, incomplete strategy% (22046)------------------------------
% 0.22/0.52  % (22046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22046)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22046)Memory used [KB]: 6396
% 0.22/0.52  % (22046)Time elapsed: 0.085 s
% 0.22/0.52  % (22046)------------------------------
% 0.22/0.52  % (22046)------------------------------
% 0.22/0.53  % (22056)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (22056)Refutation not found, incomplete strategy% (22056)------------------------------
% 0.22/0.53  % (22056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22056)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22056)Memory used [KB]: 10618
% 0.22/0.53  % (22056)Time elapsed: 0.099 s
% 0.22/0.53  % (22056)------------------------------
% 0.22/0.53  % (22056)------------------------------
% 0.22/0.53  % (22049)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (22047)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (22036)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  fof(f403,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f65,f73,f77,f81,f85,f89,f93,f97,f105,f109,f113,f121,f125,f149,f153,f162,f168,f172,f192,f200,f206,f246,f266,f331,f353,f367,f390,f402])).
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_5 | ~spl4_15 | spl4_57),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f401])).
% 0.22/0.53  fof(f401,plain,(
% 0.22/0.53    $false | (~spl4_1 | ~spl4_5 | ~spl4_15 | spl4_57)),
% 0.22/0.53    inference(subsumption_resolution,[],[f400,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    v5_relat_1(sK2,sK0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl4_5 <=> v5_relat_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    ~v5_relat_1(sK2,sK0) | (~spl4_1 | ~spl4_15 | spl4_57)),
% 0.22/0.53    inference(subsumption_resolution,[],[f398,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_1 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | (~spl4_15 | spl4_57)),
% 0.22/0.53    inference(resolution,[],[f389,f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) ) | ~spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl4_15 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | spl4_57),
% 0.22/0.53    inference(avatar_component_clause,[],[f388])).
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    spl4_57 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    ~spl4_57 | ~spl4_1 | spl4_8 | ~spl4_21 | ~spl4_54),
% 0.22/0.53    inference(avatar_split_clause,[],[f382,f365,f147,f91,f63,f388])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl4_8 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl4_21 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    spl4_54 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | (~spl4_1 | spl4_8 | ~spl4_21 | ~spl4_54)),
% 0.22/0.53    inference(subsumption_resolution,[],[f381,f64])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | (spl4_8 | ~spl4_21 | ~spl4_54)),
% 0.22/0.53    inference(subsumption_resolution,[],[f373,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) | spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | (~spl4_21 | ~spl4_54)),
% 0.22/0.53    inference(superposition,[],[f366,f148])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f147])).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0))) | ~spl4_54),
% 0.22/0.53    inference(avatar_component_clause,[],[f365])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    spl4_54 | ~spl4_52),
% 0.22/0.53    inference(avatar_split_clause,[],[f359,f351,f365])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    spl4_52 <=> ! [X8] : (sK0 != X8 | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0))) | ~spl4_52),
% 0.22/0.53    inference(equality_resolution,[],[f352])).
% 0.22/0.53  fof(f352,plain,(
% 0.22/0.53    ( ! [X8] : (sK0 != X8 | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8)))) ) | ~spl4_52),
% 0.22/0.53    inference(avatar_component_clause,[],[f351])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    spl4_52 | ~spl4_1 | ~spl4_50),
% 0.22/0.53    inference(avatar_split_clause,[],[f335,f329,f63,f351])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    spl4_50 <=> ! [X1,X0] : (sK0 != X0 | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ( ! [X8] : (sK0 != X8 | k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X8)))) ) | (~spl4_1 | ~spl4_50)),
% 0.22/0.53    inference(resolution,[],[f330,f64])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | sK0 != X0 | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1))) ) | ~spl4_50),
% 0.22/0.53    inference(avatar_component_clause,[],[f329])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    spl4_50 | ~spl4_9 | ~spl4_12 | ~spl4_40),
% 0.22/0.53    inference(avatar_split_clause,[],[f273,f264,f107,f95,f329])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_9 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl4_12 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl4_40 <=> ! [X1,X0] : (k1_relat_1(X1) != sK0 | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK0 != X0 | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1))) ) | (~spl4_9 | ~spl4_12 | ~spl4_40)),
% 0.22/0.53    inference(subsumption_resolution,[],[f271,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK0 != X0 | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,sK1)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl4_12 | ~spl4_40)),
% 0.22/0.53    inference(superposition,[],[f265,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X1)) ) | ~spl4_40),
% 0.22/0.53    inference(avatar_component_clause,[],[f264])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    spl4_40 | ~spl4_7 | ~spl4_11 | ~spl4_30 | ~spl4_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f249,f244,f190,f103,f87,f264])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl4_11 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl4_30 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    spl4_36 <=> ! [X1,X3,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(X0) != k1_relat_1(X2) | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~v1_relat_1(X3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X1)) ) | (~spl4_7 | ~spl4_11 | ~spl4_30 | ~spl4_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f248,f191])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK1) | ~spl4_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f190])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X1) != k1_relat_1(sK1) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X1)) ) | (~spl4_7 | ~spl4_11 | ~spl4_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X1) != k1_relat_1(sK1) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))) ) | (~spl4_7 | ~spl4_36)),
% 0.22/0.53    inference(resolution,[],[f245,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~v1_relat_1(X1) | k1_relat_1(X0) != k1_relat_1(X2) | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X3)) ) | ~spl4_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f244])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    spl4_36 | ~spl4_13 | ~spl4_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f178,f170,f111,f244])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl4_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl4_26 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(X0) != k1_relat_1(X2) | k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(k5_relat_1(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~v1_relat_1(X3)) ) | (~spl4_13 | ~spl4_26)),
% 0.22/0.53    inference(resolution,[],[f171,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl4_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))) ) | ~spl4_26),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_24 | spl4_29),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    $false | (~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_24 | spl4_29)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f76,f72,f84,f88,f188,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X1)) ) | ~spl4_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f160])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl4_24 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    ~v1_partfun1(sK1,sK0) | spl4_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f187])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    spl4_29 <=> v1_partfun1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl4_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    v1_funct_1(sK1) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_3 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0) | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl4_4 <=> v1_xboole_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ~spl4_7 | ~spl4_11 | ~spl4_13 | spl4_28),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f198])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    $false | (~spl4_7 | ~spl4_11 | ~spl4_13 | spl4_28)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f104,f88,f185,f112])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~v1_relat_1(sK1) | spl4_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl4_28 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ~spl4_28 | ~spl4_29 | spl4_30 | ~spl4_7 | ~spl4_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f177,f166,f87,f190,f187,f184])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    spl4_25 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK1) | ~v1_partfun1(sK1,sK0) | ~v1_relat_1(sK1) | (~spl4_7 | ~spl4_25)),
% 0.22/0.53    inference(resolution,[],[f167,f88])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl4_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f166])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl4_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f170])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl4_25 | ~spl4_16 | ~spl4_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f154,f151,f123,f166])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl4_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    spl4_22 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl4_16 | ~spl4_22)),
% 0.22/0.53    inference(resolution,[],[f152,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f123])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) ) | ~spl4_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f151])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl4_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f160])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    spl4_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f151])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl4_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f147])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl4_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f123])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl4_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f119])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f111])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f107])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f58,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f53,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(equality_resolution,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f103])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f95])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f91])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f87])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f83])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f79])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v5_relat_1(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f75])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f71])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f63])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_relat_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (22045)------------------------------
% 0.22/0.53  % (22045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22045)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (22045)Memory used [KB]: 10874
% 0.22/0.53  % (22045)Time elapsed: 0.082 s
% 0.22/0.53  % (22045)------------------------------
% 0.22/0.53  % (22045)------------------------------
% 0.22/0.53  % (22049)Refutation not found, incomplete strategy% (22049)------------------------------
% 0.22/0.53  % (22049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22049)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22049)Memory used [KB]: 1791
% 0.22/0.53  % (22049)Time elapsed: 0.056 s
% 0.22/0.53  % (22049)------------------------------
% 0.22/0.53  % (22049)------------------------------
% 0.22/0.53  % (22048)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (22035)Success in time 0.158 s
%------------------------------------------------------------------------------
