%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 285 expanded)
%              Number of leaves         :   39 ( 128 expanded)
%              Depth                    :    8
%              Number of atoms          :  520 ( 954 expanded)
%              Number of equality atoms :  101 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f58,f62,f66,f70,f74,f78,f82,f92,f104,f108,f116,f123,f127,f135,f155,f159,f179,f183,f207,f211,f267,f284,f302,f317,f321,f378,f419,f435,f449])).

% (1707)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f449,plain,
    ( ~ spl2_1
    | ~ spl2_7
    | ~ spl2_21
    | spl2_27
    | ~ spl2_40
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_21
    | spl2_27
    | ~ spl2_40
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f447,f253])).

fof(f253,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl2_40
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f447,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_21
    | spl2_27
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f446,f73])).

fof(f73,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_7
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f446,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_21
    | spl2_27
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f445,f49])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f445,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_21
    | spl2_27
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f439,f182])).

fof(f182,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_27 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl2_27
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f439,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_21
    | ~ spl2_69 ),
    inference(superposition,[],[f134,f434])).

fof(f434,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl2_69
  <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f435,plain,
    ( spl2_69
    | ~ spl2_1
    | ~ spl2_51
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f427,f417,f319,f48,f433])).

fof(f319,plain,
    ( spl2_51
  <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f417,plain,
    ( spl2_67
  <=> ! [X0] :
        ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f427,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_51
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f424,f320])).

fof(f320,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f319])).

fof(f424,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_67 ),
    inference(resolution,[],[f418,f49])).

fof(f418,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) )
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f417])).

fof(f419,plain,
    ( spl2_67
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f382,f376,f205,f60,f417])).

fof(f60,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f205,plain,
    ( spl2_31
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f376,plain,
    ( spl2_60
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f382,plain,
    ( ! [X0] :
        ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f379,f61])).

fof(f61,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f379,plain,
    ( ! [X0] :
        ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_31
    | ~ spl2_60 ),
    inference(superposition,[],[f377,f206])).

fof(f206,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f205])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl2_60
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f212,f209,f177,f376])).

fof(f177,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f209,plain,
    ( spl2_32
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1)) )
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(resolution,[],[f210,f178])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f210,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f209])).

fof(f321,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f273,f265,f106,f76,f60,f319])).

fof(f76,plain,
    ( spl2_8
  <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f106,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f265,plain,
    ( spl2_43
  <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f273,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f272,f77])).

fof(f77,plain,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f272,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f271,f61])).

fof(f271,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_15
    | ~ spl2_43 ),
    inference(superposition,[],[f266,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f266,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f265])).

fof(f317,plain,
    ( spl2_40
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f308,f300,f102,f60,f252])).

fof(f102,plain,
    ( spl2_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f300,plain,
    ( spl2_48
  <=> r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f308,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f307,f61])).

fof(f307,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_14
    | ~ spl2_48 ),
    inference(superposition,[],[f301,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f301,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f300])).

fof(f302,plain,
    ( spl2_48
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_31
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f293,f282,f205,f80,f60,f300])).

fof(f80,plain,
    ( spl2_9
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f282,plain,
    ( spl2_45
  <=> ! [X2] :
        ( ~ v1_relat_1(X2)
        | r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f293,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_31
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f292,f81])).

fof(f81,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f292,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl2_4
    | ~ spl2_31
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f289,f61])).

fof(f289,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_31
    | ~ spl2_45 ),
    inference(superposition,[],[f283,f206])).

fof(f283,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0)))
        | ~ v1_relat_1(X2) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f282])).

fof(f284,plain,
    ( spl2_45
    | ~ spl2_18
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f213,f209,f121,f282])).

fof(f121,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f213,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0))) )
    | ~ spl2_18
    | ~ spl2_32 ),
    inference(resolution,[],[f210,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f267,plain,
    ( spl2_43
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f214,f209,f114,f265])).

fof(f114,plain,
    ( spl2_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f214,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(resolution,[],[f210,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f211,plain,
    ( spl2_32
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f171,f157,f90,f64,f60,f209])).

fof(f64,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f157,plain,
    ( spl2_25
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f171,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f170,f61])).

fof(f170,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f167,f65])).

fof(f65,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f167,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(superposition,[],[f91,f158])).

fof(f158,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f91,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f207,plain,
    ( spl2_31
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f175,f157,f153,f64,f60,f56,f205])).

fof(f56,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f153,plain,
    ( spl2_24
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f175,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f174,f158])).

fof(f174,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f172,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(resolution,[],[f154,f57])).

fof(f57,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f183,plain,
    ( ~ spl2_27
    | spl2_6
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f165,f157,f68,f181])).

fof(f68,plain,
    ( spl2_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f165,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_6
    | ~ spl2_25 ),
    inference(superposition,[],[f69,f158])).

fof(f69,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f179,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f40,f177])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f159,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f142,f125,f64,f60,f56,f157])).

fof(f125,plain,
    ( spl2_19
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f142,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f141,f61])).

fof(f141,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f140,f65])).

fof(f140,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(resolution,[],[f126,f57])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k4_relat_1(X0) = k2_funct_1(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f155,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f45,f153])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f135,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f46,f133])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f127,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f43,f125])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f123,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f39,f121])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f116,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f36,f114])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f108,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f38,f106])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f104,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f82,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f78,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f74,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (801472512)
% 0.13/0.37  ipcrm: permission denied for id (801505282)
% 0.13/0.37  ipcrm: permission denied for id (805437443)
% 0.13/0.37  ipcrm: permission denied for id (805470212)
% 0.13/0.37  ipcrm: permission denied for id (801538053)
% 0.13/0.37  ipcrm: permission denied for id (807993350)
% 0.13/0.38  ipcrm: permission denied for id (801636360)
% 0.13/0.38  ipcrm: permission denied for id (805568521)
% 0.13/0.38  ipcrm: permission denied for id (801701898)
% 0.13/0.38  ipcrm: permission denied for id (805601291)
% 0.13/0.38  ipcrm: permission denied for id (808058892)
% 0.13/0.38  ipcrm: permission denied for id (805666829)
% 0.13/0.39  ipcrm: permission denied for id (805732367)
% 0.13/0.39  ipcrm: permission denied for id (808124432)
% 0.13/0.39  ipcrm: permission denied for id (805797905)
% 0.13/0.39  ipcrm: permission denied for id (801898514)
% 0.13/0.39  ipcrm: permission denied for id (801931283)
% 0.13/0.39  ipcrm: permission denied for id (801964052)
% 0.13/0.39  ipcrm: permission denied for id (801996821)
% 0.13/0.40  ipcrm: permission denied for id (802029590)
% 0.13/0.40  ipcrm: permission denied for id (808157207)
% 0.13/0.40  ipcrm: permission denied for id (808189976)
% 0.13/0.40  ipcrm: permission denied for id (805896217)
% 0.13/0.40  ipcrm: permission denied for id (805928986)
% 0.13/0.40  ipcrm: permission denied for id (808222747)
% 0.13/0.40  ipcrm: permission denied for id (805994524)
% 0.13/0.41  ipcrm: permission denied for id (808288286)
% 0.13/0.41  ipcrm: permission denied for id (808353824)
% 0.13/0.41  ipcrm: permission denied for id (802390049)
% 0.13/0.41  ipcrm: permission denied for id (802455587)
% 0.22/0.41  ipcrm: permission denied for id (802488356)
% 0.22/0.41  ipcrm: permission denied for id (802521125)
% 0.22/0.42  ipcrm: permission denied for id (806191142)
% 0.22/0.42  ipcrm: permission denied for id (802586663)
% 0.22/0.42  ipcrm: permission denied for id (802619432)
% 0.22/0.42  ipcrm: permission denied for id (802652201)
% 0.22/0.42  ipcrm: permission denied for id (802750507)
% 0.22/0.42  ipcrm: permission denied for id (802783276)
% 0.22/0.43  ipcrm: permission denied for id (802881583)
% 0.22/0.43  ipcrm: permission denied for id (806354992)
% 0.22/0.43  ipcrm: permission denied for id (806387761)
% 0.22/0.43  ipcrm: permission denied for id (802979890)
% 0.22/0.43  ipcrm: permission denied for id (808517683)
% 0.22/0.43  ipcrm: permission denied for id (803045428)
% 0.22/0.43  ipcrm: permission denied for id (806453301)
% 0.22/0.44  ipcrm: permission denied for id (803110966)
% 0.22/0.44  ipcrm: permission denied for id (803143735)
% 0.22/0.44  ipcrm: permission denied for id (806486072)
% 0.22/0.44  ipcrm: permission denied for id (806551610)
% 0.22/0.44  ipcrm: permission denied for id (808583227)
% 0.22/0.44  ipcrm: permission denied for id (803307580)
% 0.22/0.44  ipcrm: permission denied for id (803340349)
% 0.22/0.45  ipcrm: permission denied for id (803373118)
% 0.22/0.45  ipcrm: permission denied for id (803405887)
% 0.22/0.45  ipcrm: permission denied for id (803471424)
% 0.22/0.45  ipcrm: permission denied for id (808616001)
% 0.22/0.45  ipcrm: permission denied for id (803536962)
% 0.22/0.45  ipcrm: permission denied for id (803569731)
% 0.22/0.45  ipcrm: permission denied for id (803602500)
% 0.22/0.45  ipcrm: permission denied for id (806649925)
% 0.22/0.46  ipcrm: permission denied for id (803733575)
% 0.22/0.46  ipcrm: permission denied for id (806715464)
% 0.22/0.46  ipcrm: permission denied for id (803799113)
% 0.22/0.46  ipcrm: permission denied for id (808681546)
% 0.22/0.46  ipcrm: permission denied for id (803864651)
% 0.22/0.46  ipcrm: permission denied for id (803897420)
% 0.22/0.47  ipcrm: permission denied for id (806781005)
% 0.22/0.47  ipcrm: permission denied for id (808714318)
% 0.22/0.47  ipcrm: permission denied for id (803995727)
% 0.22/0.47  ipcrm: permission denied for id (806846544)
% 0.22/0.47  ipcrm: permission denied for id (804061265)
% 0.22/0.47  ipcrm: permission denied for id (804094034)
% 0.22/0.47  ipcrm: permission denied for id (804126803)
% 0.22/0.47  ipcrm: permission denied for id (804159572)
% 0.22/0.48  ipcrm: permission denied for id (804192341)
% 0.22/0.48  ipcrm: permission denied for id (804225110)
% 0.22/0.48  ipcrm: permission denied for id (804257879)
% 0.22/0.48  ipcrm: permission denied for id (808747096)
% 0.22/0.48  ipcrm: permission denied for id (806912089)
% 0.22/0.48  ipcrm: permission denied for id (806944858)
% 0.22/0.48  ipcrm: permission denied for id (804388955)
% 0.22/0.48  ipcrm: permission denied for id (806977628)
% 0.22/0.49  ipcrm: permission denied for id (808779869)
% 0.22/0.49  ipcrm: permission denied for id (804487262)
% 0.22/0.49  ipcrm: permission denied for id (804552801)
% 0.22/0.49  ipcrm: permission denied for id (807108706)
% 0.22/0.49  ipcrm: permission denied for id (807141475)
% 0.22/0.49  ipcrm: permission denied for id (804651108)
% 0.22/0.50  ipcrm: permission denied for id (807174245)
% 0.22/0.50  ipcrm: permission denied for id (804716646)
% 0.22/0.50  ipcrm: permission denied for id (808910952)
% 0.22/0.50  ipcrm: permission denied for id (804814953)
% 0.22/0.50  ipcrm: permission denied for id (804847722)
% 0.22/0.50  ipcrm: permission denied for id (804913260)
% 0.22/0.51  ipcrm: permission denied for id (804946029)
% 0.22/0.51  ipcrm: permission denied for id (807305326)
% 0.22/0.51  ipcrm: permission denied for id (805011568)
% 0.22/0.51  ipcrm: permission denied for id (807403633)
% 0.22/0.51  ipcrm: permission denied for id (807436402)
% 0.22/0.52  ipcrm: permission denied for id (807567477)
% 0.22/0.52  ipcrm: permission denied for id (807600246)
% 0.22/0.52  ipcrm: permission denied for id (807633015)
% 0.22/0.52  ipcrm: permission denied for id (807698553)
% 0.22/0.52  ipcrm: permission denied for id (807731322)
% 0.22/0.52  ipcrm: permission denied for id (807796860)
% 0.22/0.53  ipcrm: permission denied for id (807829629)
% 0.22/0.53  ipcrm: permission denied for id (807895166)
% 0.22/0.53  ipcrm: permission denied for id (807927935)
% 0.22/0.61  % (1706)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.62  % (1706)Refutation found. Thanks to Tanya!
% 0.22/0.62  % SZS status Theorem for theBenchmark
% 0.22/0.63  % (1699)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.64  % (1717)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.64  % (1717)Refutation not found, incomplete strategy% (1717)------------------------------
% 0.22/0.64  % (1717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.64  % (1717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.64  
% 0.22/0.64  % (1717)Memory used [KB]: 10618
% 0.22/0.64  % (1717)Time elapsed: 0.049 s
% 0.22/0.64  % (1717)------------------------------
% 0.22/0.64  % (1717)------------------------------
% 0.22/0.64  % SZS output start Proof for theBenchmark
% 0.22/0.64  fof(f450,plain,(
% 0.22/0.64    $false),
% 0.22/0.64    inference(avatar_sat_refutation,[],[f50,f58,f62,f66,f70,f74,f78,f82,f92,f104,f108,f116,f123,f127,f135,f155,f159,f179,f183,f207,f211,f267,f284,f302,f317,f321,f378,f419,f435,f449])).
% 0.22/0.64  % (1707)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.64  fof(f449,plain,(
% 0.22/0.64    ~spl2_1 | ~spl2_7 | ~spl2_21 | spl2_27 | ~spl2_40 | ~spl2_69),
% 0.22/0.64    inference(avatar_contradiction_clause,[],[f448])).
% 0.22/0.64  fof(f448,plain,(
% 0.22/0.64    $false | (~spl2_1 | ~spl2_7 | ~spl2_21 | spl2_27 | ~spl2_40 | ~spl2_69)),
% 0.22/0.64    inference(subsumption_resolution,[],[f447,f253])).
% 0.22/0.64  fof(f253,plain,(
% 0.22/0.64    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~spl2_40),
% 0.22/0.64    inference(avatar_component_clause,[],[f252])).
% 0.22/0.64  fof(f252,plain,(
% 0.22/0.64    spl2_40 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.64  fof(f447,plain,(
% 0.22/0.64    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl2_1 | ~spl2_7 | ~spl2_21 | spl2_27 | ~spl2_69)),
% 0.22/0.64    inference(forward_demodulation,[],[f446,f73])).
% 0.22/0.64  fof(f73,plain,(
% 0.22/0.64    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_7),
% 0.22/0.64    inference(avatar_component_clause,[],[f72])).
% 0.22/0.64  fof(f72,plain,(
% 0.22/0.64    spl2_7 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.64  fof(f446,plain,(
% 0.22/0.64    ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0)) | (~spl2_1 | ~spl2_21 | spl2_27 | ~spl2_69)),
% 0.22/0.64    inference(subsumption_resolution,[],[f445,f49])).
% 0.22/0.64  fof(f49,plain,(
% 0.22/0.64    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.64    inference(avatar_component_clause,[],[f48])).
% 0.22/0.64  fof(f48,plain,(
% 0.22/0.64    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.64  fof(f445,plain,(
% 0.22/0.64    ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK1) | (~spl2_21 | spl2_27 | ~spl2_69)),
% 0.22/0.64    inference(subsumption_resolution,[],[f439,f182])).
% 0.22/0.64  fof(f182,plain,(
% 0.22/0.64    sK1 != k4_relat_1(sK0) | spl2_27),
% 0.22/0.64    inference(avatar_component_clause,[],[f181])).
% 0.22/0.64  fof(f181,plain,(
% 0.22/0.64    spl2_27 <=> sK1 = k4_relat_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.64  fof(f439,plain,(
% 0.22/0.64    sK1 = k4_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK1) | (~spl2_21 | ~spl2_69)),
% 0.22/0.64    inference(superposition,[],[f134,f434])).
% 0.22/0.64  fof(f434,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~spl2_69),
% 0.22/0.64    inference(avatar_component_clause,[],[f433])).
% 0.22/0.64  fof(f433,plain,(
% 0.22/0.64    spl2_69 <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.22/0.64  fof(f134,plain,(
% 0.22/0.64    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_21),
% 0.22/0.64    inference(avatar_component_clause,[],[f133])).
% 0.22/0.64  fof(f133,plain,(
% 0.22/0.64    spl2_21 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.64  fof(f435,plain,(
% 0.22/0.64    spl2_69 | ~spl2_1 | ~spl2_51 | ~spl2_67),
% 0.22/0.64    inference(avatar_split_clause,[],[f427,f417,f319,f48,f433])).
% 0.22/0.64  fof(f319,plain,(
% 0.22/0.64    spl2_51 <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.64  fof(f417,plain,(
% 0.22/0.64    spl2_67 <=> ! [X0] : (k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) | ~v1_relat_1(X0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.22/0.64  fof(f427,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_51 | ~spl2_67)),
% 0.22/0.64    inference(forward_demodulation,[],[f424,f320])).
% 0.22/0.64  fof(f320,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) | ~spl2_51),
% 0.22/0.64    inference(avatar_component_clause,[],[f319])).
% 0.22/0.64  fof(f424,plain,(
% 0.22/0.64    k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_67)),
% 0.22/0.64    inference(resolution,[],[f418,f49])).
% 0.22/0.64  fof(f418,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) ) | ~spl2_67),
% 0.22/0.64    inference(avatar_component_clause,[],[f417])).
% 0.22/0.64  fof(f419,plain,(
% 0.22/0.64    spl2_67 | ~spl2_4 | ~spl2_31 | ~spl2_60),
% 0.22/0.64    inference(avatar_split_clause,[],[f382,f376,f205,f60,f417])).
% 0.22/0.64  fof(f60,plain,(
% 0.22/0.64    spl2_4 <=> v1_relat_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.64  fof(f205,plain,(
% 0.22/0.64    spl2_31 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.64  fof(f376,plain,(
% 0.22/0.64    spl2_60 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 0.22/0.64  fof(f382,plain,(
% 0.22/0.64    ( ! [X0] : (k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_31 | ~spl2_60)),
% 0.22/0.64    inference(subsumption_resolution,[],[f379,f61])).
% 0.22/0.64  fof(f61,plain,(
% 0.22/0.64    v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.64    inference(avatar_component_clause,[],[f60])).
% 0.22/0.64  fof(f379,plain,(
% 0.22/0.64    ( ! [X0] : (k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | (~spl2_31 | ~spl2_60)),
% 0.22/0.64    inference(superposition,[],[f377,f206])).
% 0.22/0.64  fof(f206,plain,(
% 0.22/0.64    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | ~spl2_31),
% 0.22/0.64    inference(avatar_component_clause,[],[f205])).
% 0.22/0.64  fof(f377,plain,(
% 0.22/0.64    ( ! [X0,X1] : (k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_60),
% 0.22/0.64    inference(avatar_component_clause,[],[f376])).
% 0.22/0.64  fof(f378,plain,(
% 0.22/0.64    spl2_60 | ~spl2_26 | ~spl2_32),
% 0.22/0.64    inference(avatar_split_clause,[],[f212,f209,f177,f376])).
% 0.22/0.64  fof(f177,plain,(
% 0.22/0.64    spl2_26 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.64  fof(f209,plain,(
% 0.22/0.64    spl2_32 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.64  fof(f212,plain,(
% 0.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1))) ) | (~spl2_26 | ~spl2_32)),
% 0.22/0.64    inference(resolution,[],[f210,f178])).
% 0.22/0.64  fof(f178,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) ) | ~spl2_26),
% 0.22/0.64    inference(avatar_component_clause,[],[f177])).
% 0.22/0.64  fof(f210,plain,(
% 0.22/0.64    v1_relat_1(k4_relat_1(sK0)) | ~spl2_32),
% 0.22/0.64    inference(avatar_component_clause,[],[f209])).
% 0.22/0.64  fof(f321,plain,(
% 0.22/0.64    spl2_51 | ~spl2_4 | ~spl2_8 | ~spl2_15 | ~spl2_43),
% 0.22/0.64    inference(avatar_split_clause,[],[f273,f265,f106,f76,f60,f319])).
% 0.22/0.64  fof(f76,plain,(
% 0.22/0.64    spl2_8 <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.64  fof(f106,plain,(
% 0.22/0.64    spl2_15 <=> ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.64  fof(f265,plain,(
% 0.22/0.64    spl2_43 <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.64  fof(f273,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) | (~spl2_4 | ~spl2_8 | ~spl2_15 | ~spl2_43)),
% 0.22/0.64    inference(forward_demodulation,[],[f272,f77])).
% 0.22/0.64  fof(f77,plain,(
% 0.22/0.64    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) | ~spl2_8),
% 0.22/0.64    inference(avatar_component_clause,[],[f76])).
% 0.22/0.64  fof(f272,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl2_4 | ~spl2_15 | ~spl2_43)),
% 0.22/0.64    inference(subsumption_resolution,[],[f271,f61])).
% 0.22/0.64  fof(f271,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | (~spl2_15 | ~spl2_43)),
% 0.22/0.64    inference(superposition,[],[f266,f107])).
% 0.22/0.64  fof(f107,plain,(
% 0.22/0.64    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_15),
% 0.22/0.64    inference(avatar_component_clause,[],[f106])).
% 0.22/0.64  fof(f266,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) | ~spl2_43),
% 0.22/0.64    inference(avatar_component_clause,[],[f265])).
% 0.22/0.64  fof(f317,plain,(
% 0.22/0.64    spl2_40 | ~spl2_4 | ~spl2_14 | ~spl2_48),
% 0.22/0.64    inference(avatar_split_clause,[],[f308,f300,f102,f60,f252])).
% 0.22/0.64  fof(f102,plain,(
% 0.22/0.64    spl2_14 <=> ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.64  fof(f300,plain,(
% 0.22/0.64    spl2_48 <=> r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.22/0.64  fof(f308,plain,(
% 0.22/0.64    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl2_4 | ~spl2_14 | ~spl2_48)),
% 0.22/0.64    inference(subsumption_resolution,[],[f307,f61])).
% 0.22/0.64  fof(f307,plain,(
% 0.22/0.64    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_14 | ~spl2_48)),
% 0.22/0.64    inference(superposition,[],[f301,f103])).
% 0.22/0.64  fof(f103,plain,(
% 0.22/0.64    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.22/0.64    inference(avatar_component_clause,[],[f102])).
% 0.22/0.64  fof(f301,plain,(
% 0.22/0.64    r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~spl2_48),
% 0.22/0.64    inference(avatar_component_clause,[],[f300])).
% 0.22/0.64  fof(f302,plain,(
% 0.22/0.64    spl2_48 | ~spl2_4 | ~spl2_9 | ~spl2_31 | ~spl2_45),
% 0.22/0.64    inference(avatar_split_clause,[],[f293,f282,f205,f80,f60,f300])).
% 0.22/0.64  fof(f80,plain,(
% 0.22/0.64    spl2_9 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.64  fof(f282,plain,(
% 0.22/0.64    spl2_45 <=> ! [X2] : (~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0))))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.64  fof(f293,plain,(
% 0.22/0.64    r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | (~spl2_4 | ~spl2_9 | ~spl2_31 | ~spl2_45)),
% 0.22/0.64    inference(forward_demodulation,[],[f292,f81])).
% 0.22/0.64  fof(f81,plain,(
% 0.22/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_9),
% 0.22/0.64    inference(avatar_component_clause,[],[f80])).
% 0.22/0.64  fof(f292,plain,(
% 0.22/0.64    r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | (~spl2_4 | ~spl2_31 | ~spl2_45)),
% 0.22/0.64    inference(subsumption_resolution,[],[f289,f61])).
% 0.22/0.64  fof(f289,plain,(
% 0.22/0.64    r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(sK0) | (~spl2_31 | ~spl2_45)),
% 0.22/0.64    inference(superposition,[],[f283,f206])).
% 0.22/0.64  fof(f283,plain,(
% 0.22/0.64    ( ! [X2] : (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(X2)) ) | ~spl2_45),
% 0.22/0.64    inference(avatar_component_clause,[],[f282])).
% 0.22/0.64  fof(f284,plain,(
% 0.22/0.64    spl2_45 | ~spl2_18 | ~spl2_32),
% 0.22/0.64    inference(avatar_split_clause,[],[f213,f209,f121,f282])).
% 0.22/0.64  fof(f121,plain,(
% 0.22/0.64    spl2_18 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.64  fof(f213,plain,(
% 0.22/0.64    ( ! [X2] : (~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k1_relat_1(k4_relat_1(sK0)))) ) | (~spl2_18 | ~spl2_32)),
% 0.22/0.64    inference(resolution,[],[f210,f122])).
% 0.22/0.64  fof(f122,plain,(
% 0.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))) ) | ~spl2_18),
% 0.22/0.64    inference(avatar_component_clause,[],[f121])).
% 0.22/0.64  fof(f267,plain,(
% 0.22/0.64    spl2_43 | ~spl2_17 | ~spl2_32),
% 0.22/0.64    inference(avatar_split_clause,[],[f214,f209,f114,f265])).
% 0.22/0.64  fof(f114,plain,(
% 0.22/0.64    spl2_17 <=> ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.64  fof(f214,plain,(
% 0.22/0.64    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) | (~spl2_17 | ~spl2_32)),
% 0.22/0.64    inference(resolution,[],[f210,f115])).
% 0.22/0.64  fof(f115,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_17),
% 0.22/0.64    inference(avatar_component_clause,[],[f114])).
% 0.22/0.64  fof(f211,plain,(
% 0.22/0.64    spl2_32 | ~spl2_4 | ~spl2_5 | ~spl2_11 | ~spl2_25),
% 0.22/0.64    inference(avatar_split_clause,[],[f171,f157,f90,f64,f60,f209])).
% 0.22/0.64  fof(f64,plain,(
% 0.22/0.64    spl2_5 <=> v1_funct_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.64  fof(f90,plain,(
% 0.22/0.64    spl2_11 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.64  fof(f157,plain,(
% 0.22/0.64    spl2_25 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.64  fof(f171,plain,(
% 0.22/0.64    v1_relat_1(k4_relat_1(sK0)) | (~spl2_4 | ~spl2_5 | ~spl2_11 | ~spl2_25)),
% 0.22/0.64    inference(subsumption_resolution,[],[f170,f61])).
% 0.22/0.64  fof(f170,plain,(
% 0.22/0.64    v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_11 | ~spl2_25)),
% 0.22/0.64    inference(subsumption_resolution,[],[f167,f65])).
% 0.22/0.64  fof(f65,plain,(
% 0.22/0.64    v1_funct_1(sK0) | ~spl2_5),
% 0.22/0.64    inference(avatar_component_clause,[],[f64])).
% 0.22/0.64  fof(f167,plain,(
% 0.22/0.64    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_11 | ~spl2_25)),
% 0.22/0.64    inference(superposition,[],[f91,f158])).
% 0.22/0.64  fof(f158,plain,(
% 0.22/0.64    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_25),
% 0.22/0.64    inference(avatar_component_clause,[],[f157])).
% 0.22/0.64  fof(f91,plain,(
% 0.22/0.64    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_11),
% 0.22/0.64    inference(avatar_component_clause,[],[f90])).
% 0.22/0.64  fof(f207,plain,(
% 0.22/0.64    spl2_31 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_24 | ~spl2_25),
% 0.22/0.64    inference(avatar_split_clause,[],[f175,f157,f153,f64,f60,f56,f205])).
% 0.22/0.64  fof(f56,plain,(
% 0.22/0.64    spl2_3 <=> v2_funct_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.64  fof(f153,plain,(
% 0.22/0.64    spl2_24 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.64  fof(f175,plain,(
% 0.22/0.64    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_24 | ~spl2_25)),
% 0.22/0.64    inference(forward_demodulation,[],[f174,f158])).
% 0.22/0.64  fof(f174,plain,(
% 0.22/0.64    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_24)),
% 0.22/0.64    inference(subsumption_resolution,[],[f173,f61])).
% 0.22/0.64  fof(f173,plain,(
% 0.22/0.64    ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_5 | ~spl2_24)),
% 0.22/0.64    inference(subsumption_resolution,[],[f172,f65])).
% 0.22/0.64  fof(f172,plain,(
% 0.22/0.64    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_24)),
% 0.22/0.64    inference(resolution,[],[f154,f57])).
% 0.22/0.64  fof(f57,plain,(
% 0.22/0.64    v2_funct_1(sK0) | ~spl2_3),
% 0.22/0.64    inference(avatar_component_clause,[],[f56])).
% 0.22/0.64  fof(f154,plain,(
% 0.22/0.64    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) ) | ~spl2_24),
% 0.22/0.64    inference(avatar_component_clause,[],[f153])).
% 0.22/0.64  fof(f183,plain,(
% 0.22/0.64    ~spl2_27 | spl2_6 | ~spl2_25),
% 0.22/0.64    inference(avatar_split_clause,[],[f165,f157,f68,f181])).
% 0.22/0.64  fof(f68,plain,(
% 0.22/0.64    spl2_6 <=> sK1 = k2_funct_1(sK0)),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.64  fof(f165,plain,(
% 0.22/0.64    sK1 != k4_relat_1(sK0) | (spl2_6 | ~spl2_25)),
% 0.22/0.64    inference(superposition,[],[f69,f158])).
% 0.22/0.64  fof(f69,plain,(
% 0.22/0.64    sK1 != k2_funct_1(sK0) | spl2_6),
% 0.22/0.64    inference(avatar_component_clause,[],[f68])).
% 0.22/0.64  fof(f179,plain,(
% 0.22/0.64    spl2_26),
% 0.22/0.64    inference(avatar_split_clause,[],[f40,f177])).
% 0.22/0.64  fof(f40,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f17])).
% 0.22/0.64  fof(f17,plain,(
% 0.22/0.64    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(ennf_transformation,[],[f3])).
% 0.22/0.64  fof(f3,axiom,(
% 0.22/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.64  fof(f159,plain,(
% 0.22/0.64    spl2_25 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_19),
% 0.22/0.64    inference(avatar_split_clause,[],[f142,f125,f64,f60,f56,f157])).
% 0.22/0.64  fof(f125,plain,(
% 0.22/0.64    spl2_19 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0))),
% 0.22/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.64  fof(f142,plain,(
% 0.22/0.64    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_19)),
% 0.22/0.64    inference(subsumption_resolution,[],[f141,f61])).
% 0.22/0.64  fof(f141,plain,(
% 0.22/0.64    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_19)),
% 0.22/0.64    inference(subsumption_resolution,[],[f140,f65])).
% 0.22/0.64  fof(f140,plain,(
% 0.22/0.64    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_19)),
% 0.22/0.64    inference(resolution,[],[f126,f57])).
% 0.22/0.64  fof(f126,plain,(
% 0.22/0.64    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) ) | ~spl2_19),
% 0.22/0.64    inference(avatar_component_clause,[],[f125])).
% 0.22/0.64  fof(f155,plain,(
% 0.22/0.64    spl2_24),
% 0.22/0.64    inference(avatar_split_clause,[],[f45,f153])).
% 0.22/0.64  fof(f45,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f23])).
% 0.22/0.64  fof(f23,plain,(
% 0.22/0.64    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(flattening,[],[f22])).
% 0.22/0.64  fof(f22,plain,(
% 0.22/0.64    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.64    inference(ennf_transformation,[],[f9])).
% 0.22/0.64  fof(f9,axiom,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.64  fof(f135,plain,(
% 0.22/0.64    spl2_21),
% 0.22/0.64    inference(avatar_split_clause,[],[f46,f133])).
% 0.22/0.64  fof(f46,plain,(
% 0.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.22/0.64    inference(cnf_transformation,[],[f25])).
% 0.22/0.64  fof(f25,plain,(
% 0.22/0.64    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.64    inference(flattening,[],[f24])).
% 0.22/0.64  fof(f24,plain,(
% 0.22/0.64    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.64    inference(ennf_transformation,[],[f5])).
% 0.22/0.64  fof(f5,axiom,(
% 0.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.64  fof(f127,plain,(
% 0.22/0.64    spl2_19),
% 0.22/0.64    inference(avatar_split_clause,[],[f43,f125])).
% 0.22/0.64  fof(f43,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f21])).
% 0.22/0.64  fof(f21,plain,(
% 0.22/0.64    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(flattening,[],[f20])).
% 0.22/0.64  fof(f20,plain,(
% 0.22/0.64    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.64    inference(ennf_transformation,[],[f7])).
% 0.22/0.64  fof(f7,axiom,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.64  fof(f123,plain,(
% 0.22/0.64    spl2_18),
% 0.22/0.64    inference(avatar_split_clause,[],[f39,f121])).
% 0.22/0.64  fof(f39,plain,(
% 0.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f16])).
% 0.22/0.64  fof(f16,plain,(
% 0.22/0.64    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(ennf_transformation,[],[f2])).
% 0.22/0.64  fof(f2,axiom,(
% 0.22/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.64  fof(f116,plain,(
% 0.22/0.64    spl2_17),
% 0.22/0.64    inference(avatar_split_clause,[],[f36,f114])).
% 0.22/0.64  fof(f36,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.22/0.64    inference(cnf_transformation,[],[f14])).
% 0.22/0.64  fof(f14,plain,(
% 0.22/0.64    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.64    inference(ennf_transformation,[],[f6])).
% 0.22/0.64  fof(f6,axiom,(
% 0.22/0.64    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.64  fof(f108,plain,(
% 0.22/0.64    spl2_15),
% 0.22/0.64    inference(avatar_split_clause,[],[f38,f106])).
% 0.22/0.64  fof(f38,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f15])).
% 0.22/0.64  fof(f15,plain,(
% 0.22/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(ennf_transformation,[],[f1])).
% 0.22/0.64  fof(f1,axiom,(
% 0.22/0.64    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.64  fof(f104,plain,(
% 0.22/0.64    spl2_14),
% 0.22/0.64    inference(avatar_split_clause,[],[f37,f102])).
% 0.22/0.64  fof(f37,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f15])).
% 0.22/0.64  fof(f92,plain,(
% 0.22/0.64    spl2_11),
% 0.22/0.64    inference(avatar_split_clause,[],[f41,f90])).
% 0.22/0.64  fof(f41,plain,(
% 0.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f19])).
% 0.22/0.64  fof(f19,plain,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.64    inference(flattening,[],[f18])).
% 0.22/0.64  fof(f18,plain,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.64    inference(ennf_transformation,[],[f8])).
% 0.22/0.64  fof(f8,axiom,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.64  fof(f82,plain,(
% 0.22/0.64    spl2_9),
% 0.22/0.64    inference(avatar_split_clause,[],[f34,f80])).
% 0.22/0.64  fof(f34,plain,(
% 0.22/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.64    inference(cnf_transformation,[],[f4])).
% 0.22/0.64  fof(f4,axiom,(
% 0.22/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.64  fof(f78,plain,(
% 0.22/0.64    spl2_8),
% 0.22/0.64    inference(avatar_split_clause,[],[f30,f76])).
% 0.22/0.64  fof(f30,plain,(
% 0.22/0.64    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f13,plain,(
% 0.22/0.64    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.64    inference(flattening,[],[f12])).
% 0.22/0.64  fof(f12,plain,(
% 0.22/0.64    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.64    inference(ennf_transformation,[],[f11])).
% 0.22/0.64  fof(f11,negated_conjecture,(
% 0.22/0.64    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.64    inference(negated_conjecture,[],[f10])).
% 0.22/0.64  fof(f10,conjecture,(
% 0.22/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.64  fof(f74,plain,(
% 0.22/0.64    spl2_7),
% 0.22/0.64    inference(avatar_split_clause,[],[f29,f72])).
% 0.22/0.64  fof(f29,plain,(
% 0.22/0.64    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f70,plain,(
% 0.22/0.64    ~spl2_6),
% 0.22/0.64    inference(avatar_split_clause,[],[f31,f68])).
% 0.22/0.64  fof(f31,plain,(
% 0.22/0.64    sK1 != k2_funct_1(sK0)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f66,plain,(
% 0.22/0.64    spl2_5),
% 0.22/0.64    inference(avatar_split_clause,[],[f33,f64])).
% 0.22/0.64  fof(f33,plain,(
% 0.22/0.64    v1_funct_1(sK0)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f62,plain,(
% 0.22/0.64    spl2_4),
% 0.22/0.64    inference(avatar_split_clause,[],[f32,f60])).
% 0.22/0.64  fof(f32,plain,(
% 0.22/0.64    v1_relat_1(sK0)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f58,plain,(
% 0.22/0.64    spl2_3),
% 0.22/0.64    inference(avatar_split_clause,[],[f28,f56])).
% 0.22/0.64  fof(f28,plain,(
% 0.22/0.64    v2_funct_1(sK0)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f50,plain,(
% 0.22/0.64    spl2_1),
% 0.22/0.64    inference(avatar_split_clause,[],[f26,f48])).
% 0.22/0.64  fof(f26,plain,(
% 0.22/0.64    v1_relat_1(sK1)),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  % SZS output end Proof for theBenchmark
% 0.22/0.64  % (1706)------------------------------
% 0.22/0.64  % (1706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.64  % (1706)Termination reason: Refutation
% 0.22/0.64  
% 0.22/0.64  % (1706)Memory used [KB]: 10874
% 0.22/0.64  % (1706)Time elapsed: 0.047 s
% 0.22/0.64  % (1706)------------------------------
% 0.22/0.64  % (1706)------------------------------
% 0.22/0.64  % (1560)Success in time 0.281 s
%------------------------------------------------------------------------------
