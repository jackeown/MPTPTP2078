%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 223 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :    6
%              Number of atoms          :  386 ( 672 expanded)
%              Number of equality atoms :   86 ( 169 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f54,f63,f67,f80,f88,f96,f104,f108,f172,f301,f311,f337,f374,f401,f444,f463,f477,f542,f591,f608,f629,f663,f707,f730,f759])).

fof(f759,plain,
    ( spl8_2
    | ~ spl8_47
    | ~ spl8_64 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | spl8_2
    | ~ spl8_47
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f740,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f740,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_47
    | ~ spl8_64 ),
    inference(resolution,[],[f703,f476])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_xboole_0,X0,X1),X1)
        | k1_xboole_0 = X1 )
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl8_47
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X1
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f703,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl8_64
  <=> ! [X5] : ~ r2_hidden(X5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f730,plain,
    ( spl8_4
    | ~ spl8_7
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(avatar_contradiction_clause,[],[f729])).

fof(f729,plain,
    ( $false
    | spl8_4
    | ~ spl8_7
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f728,f47])).

fof(f47,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f728,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f717,f62])).

fof(f62,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_7
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f717,plain,
    ( ! [X20] : sK0 = k4_xboole_0(k1_xboole_0,X20)
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(resolution,[],[f706,f628])).

fof(f628,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_xboole_0)
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl8_62
  <=> ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f706,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(X3,X4,sK0),X3)
        | sK0 = k4_xboole_0(X3,X4) )
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl8_65
  <=> ! [X3,X4] :
        ( sK0 = k4_xboole_0(X3,X4)
        | r2_hidden(sK2(X3,X4,sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f707,plain,
    ( spl8_64
    | spl8_65
    | ~ spl8_5
    | ~ spl8_34
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f695,f627,f299,f50,f705,f702])).

fof(f50,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f299,plain,
    ( spl8_34
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2
        | ~ r2_hidden(X3,X4)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f695,plain,
    ( ! [X4,X5,X3] :
        ( sK0 = k4_xboole_0(X3,X4)
        | ~ r2_hidden(X5,sK1)
        | r2_hidden(sK2(X3,X4,sK0),X3) )
    | ~ spl8_5
    | ~ spl8_34
    | ~ spl8_62 ),
    inference(subsumption_resolution,[],[f683,f628])).

fof(f683,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(k4_tarski(sK2(X3,X4,sK0),X5),k1_xboole_0)
        | sK0 = k4_xboole_0(X3,X4)
        | ~ r2_hidden(X5,sK1)
        | r2_hidden(sK2(X3,X4,sK0),X3) )
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(superposition,[],[f300,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f300,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4))
        | k4_xboole_0(X0,X1) = X2
        | ~ r2_hidden(X3,X4)
        | r2_hidden(sK2(X0,X1,X2),X0) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f299])).

fof(f663,plain,
    ( spl8_1
    | ~ spl8_18
    | ~ spl8_62 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | spl8_1
    | ~ spl8_18
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f37,f628,f628,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_18
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f37,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f629,plain,
    ( spl8_62
    | ~ spl8_52
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f619,f606,f540,f627])).

fof(f540,plain,
    ( spl8_52
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(sK5(k1_xboole_0,X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f606,plain,
    ( spl8_60
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f619,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_xboole_0)
    | ~ spl8_52
    | ~ spl8_60 ),
    inference(duplicate_literal_removal,[],[f618])).

fof(f618,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | ~ spl8_52
    | ~ spl8_60 ),
    inference(resolution,[],[f607,f541])).

fof(f541,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f540])).

fof(f607,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f606])).

fof(f608,plain,
    ( spl8_60
    | ~ spl8_7
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f598,f589,f61,f606])).

fof(f589,plain,
    ( spl8_57
  <=> ! [X9,X7,X8] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | ~ r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f598,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl8_7
    | ~ spl8_57 ),
    inference(superposition,[],[f590,f62])).

fof(f590,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8))
        | ~ r2_hidden(X7,k1_xboole_0) )
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f589])).

fof(f591,plain,
    ( spl8_57
    | ~ spl8_8
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f558,f540,f65,f589])).

fof(f65,plain,
    ( spl8_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f558,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | ~ r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8)) )
    | ~ spl8_8
    | ~ spl8_52 ),
    inference(resolution,[],[f541,f66])).

fof(f66,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f542,plain,
    ( spl8_52
    | ~ spl8_11
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f452,f442,f78,f540])).

fof(f78,plain,
    ( spl8_11
  <=> ! [X1,X3,X0] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f442,plain,
    ( spl8_45
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(sK5(k1_xboole_0,X0,X1),X0) )
    | ~ spl8_11
    | ~ spl8_45 ),
    inference(superposition,[],[f79,f443])).

fof(f443,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f442])).

fof(f79,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
        | r2_hidden(sK5(X0,X1,X3),X1) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f477,plain,
    ( spl8_47
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f417,f399,f335,f475])).

fof(f335,plain,
    ( spl8_38
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(k1_xboole_0,X0) = X1
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f399,plain,
    ( spl8_43
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0)
        | k2_zfmisc_1(k1_xboole_0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) )
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(backward_demodulation,[],[f336,f415])).

fof(f415,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(duplicate_literal_removal,[],[f414])).

fof(f414,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) )
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(resolution,[],[f400,f336])).

fof(f400,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0)
        | k2_zfmisc_1(k1_xboole_0,X1) = X0 )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f399])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_xboole_0,X0,X1),X1)
        | k2_zfmisc_1(k1_xboole_0,X0) = X1 )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f335])).

fof(f463,plain,
    ( spl8_3
    | ~ spl8_45 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl8_3
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f44,f443])).

fof(f44,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f444,plain,
    ( spl8_45
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f415,f399,f335,f442])).

fof(f401,plain,
    ( spl8_43
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f379,f372,f61,f399])).

fof(f372,plain,
    ( spl8_40
  <=> ! [X9,X7,X8] :
        ( k2_zfmisc_1(k1_xboole_0,X7) = X8
        | ~ r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0)
        | k2_zfmisc_1(k1_xboole_0,X1) = X0 )
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(superposition,[],[f373,f62])).

fof(f373,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8))
        | k2_zfmisc_1(k1_xboole_0,X7) = X8 )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f372])).

fof(f374,plain,
    ( spl8_40
    | ~ spl8_8
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f346,f335,f65,f372])).

fof(f346,plain,
    ( ! [X8,X7,X9] :
        ( k2_zfmisc_1(k1_xboole_0,X7) = X8
        | ~ r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8)) )
    | ~ spl8_8
    | ~ spl8_38 ),
    inference(resolution,[],[f336,f66])).

fof(f337,plain,
    ( spl8_38
    | ~ spl8_17
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f319,f309,f102,f335])).

fof(f102,plain,
    ( spl8_17
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

% (13749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f309,plain,
    ( spl8_35
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK6(X0,X1,X2),k1_xboole_0)
        | k2_zfmisc_1(X0,X1) = X2
        | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(k1_xboole_0,X0) = X1
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) )
    | ~ spl8_17
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(k1_xboole_0,X0) = X1
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1)
        | r2_hidden(sK3(k1_xboole_0,X0,X1),X1)
        | k2_zfmisc_1(k1_xboole_0,X0) = X1 )
    | ~ spl8_17
    | ~ spl8_35 ),
    inference(resolution,[],[f310,f103])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK6(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f102])).

fof(f310,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6(X0,X1,X2),k1_xboole_0)
        | k2_zfmisc_1(X0,X1) = X2
        | r2_hidden(sK3(X0,X1,X2),X2) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f309])).

fof(f311,plain,
    ( spl8_35
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f177,f170,f61,f309])).

fof(f170,plain,
    ( spl8_26
  <=> ! [X9,X11,X10,X12] :
        ( r2_hidden(sK3(X9,X10,X11),X11)
        | k2_zfmisc_1(X9,X10) = X11
        | ~ r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6(X0,X1,X2),k1_xboole_0)
        | k2_zfmisc_1(X0,X1) = X2
        | r2_hidden(sK3(X0,X1,X2),X2) )
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(superposition,[],[f171,f62])).

fof(f171,plain,
    ( ! [X12,X10,X11,X9] :
        ( ~ r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9))
        | k2_zfmisc_1(X9,X10) = X11
        | r2_hidden(sK3(X9,X10,X11),X11) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f170])).

fof(f301,plain,
    ( spl8_34
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f109,f94,f86,f299])).

fof(f86,plain,
    ( spl8_13
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f94,plain,
    ( spl8_15
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(sK2(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f109,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2
        | ~ r2_hidden(X3,X4)
        | r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4)) )
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(resolution,[],[f95,f87])).

fof(f87,plain,
    ( ! [X4,X0,X5,X1] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f172,plain,
    ( spl8_26
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f126,f102,f65,f170])).

fof(f126,plain,
    ( ! [X12,X10,X11,X9] :
        ( r2_hidden(sK3(X9,X10,X11),X11)
        | k2_zfmisc_1(X9,X10) = X11
        | ~ r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9)) )
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(resolution,[],[f103,f66])).

fof(f108,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f19,f106])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f104,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f18,f102])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f96,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f12,f94])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f88,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f29,f86])).

fof(f29,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f10,f61])).

fof(f10,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f54,plain,
    ( spl8_5
    | spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f9,f46,f39,f50])).

fof(f9,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f34,f46,f43])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f7])).

fof(f7,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f33,f39,f36])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (13748)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (13750)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (13756)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (13744)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (13761)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (13751)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (13746)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (13752)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (13746)Refutation not found, incomplete strategy% (13746)------------------------------
% 0.21/0.50  % (13746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13746)Memory used [KB]: 10618
% 0.21/0.50  % (13746)Time elapsed: 0.082 s
% 0.21/0.50  % (13746)------------------------------
% 0.21/0.50  % (13746)------------------------------
% 0.21/0.50  % (13743)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (13743)Refutation not found, incomplete strategy% (13743)------------------------------
% 0.21/0.50  % (13743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13743)Memory used [KB]: 6140
% 0.21/0.50  % (13743)Time elapsed: 0.079 s
% 0.21/0.50  % (13743)------------------------------
% 0.21/0.50  % (13743)------------------------------
% 0.21/0.50  % (13744)Refutation not found, incomplete strategy% (13744)------------------------------
% 0.21/0.50  % (13744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13763)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (13744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13744)Memory used [KB]: 10618
% 0.21/0.50  % (13744)Time elapsed: 0.084 s
% 0.21/0.50  % (13744)------------------------------
% 0.21/0.50  % (13744)------------------------------
% 0.21/0.50  % (13754)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (13763)Refutation not found, incomplete strategy% (13763)------------------------------
% 0.21/0.50  % (13763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13763)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13763)Memory used [KB]: 10618
% 0.21/0.50  % (13763)Time elapsed: 0.043 s
% 0.21/0.50  % (13763)------------------------------
% 0.21/0.50  % (13763)------------------------------
% 0.21/0.51  % (13762)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (13755)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13755)Refutation not found, incomplete strategy% (13755)------------------------------
% 0.21/0.51  % (13755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13754)Refutation not found, incomplete strategy% (13754)------------------------------
% 0.21/0.51  % (13754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13754)Memory used [KB]: 10618
% 0.21/0.51  % (13754)Time elapsed: 0.097 s
% 0.21/0.51  % (13754)------------------------------
% 0.21/0.51  % (13754)------------------------------
% 0.21/0.52  % (13745)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (13759)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (13758)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (13747)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (13752)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f760,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f41,f48,f54,f63,f67,f80,f88,f96,f104,f108,f172,f301,f311,f337,f374,f401,f444,f463,f477,f542,f591,f608,f629,f663,f707,f730,f759])).
% 0.21/0.52  fof(f759,plain,(
% 0.21/0.52    spl8_2 | ~spl8_47 | ~spl8_64),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f758])).
% 0.21/0.52  fof(f758,plain,(
% 0.21/0.52    $false | (spl8_2 | ~spl8_47 | ~spl8_64)),
% 0.21/0.52    inference(subsumption_resolution,[],[f740,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f740,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (~spl8_47 | ~spl8_64)),
% 0.21/0.52    inference(resolution,[],[f703,f476])).
% 0.21/0.52  fof(f476,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(k1_xboole_0,X0,X1),X1) | k1_xboole_0 = X1) ) | ~spl8_47),
% 0.21/0.52    inference(avatar_component_clause,[],[f475])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    spl8_47 <=> ! [X1,X0] : (k1_xboole_0 = X1 | r2_hidden(sK3(k1_xboole_0,X0,X1),X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.21/0.52  fof(f703,plain,(
% 0.21/0.52    ( ! [X5] : (~r2_hidden(X5,sK1)) ) | ~spl8_64),
% 0.21/0.52    inference(avatar_component_clause,[],[f702])).
% 0.21/0.52  fof(f702,plain,(
% 0.21/0.52    spl8_64 <=> ! [X5] : ~r2_hidden(X5,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 0.21/0.52  fof(f730,plain,(
% 0.21/0.52    spl8_4 | ~spl8_7 | ~spl8_62 | ~spl8_65),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f729])).
% 0.21/0.52  fof(f729,plain,(
% 0.21/0.52    $false | (spl8_4 | ~spl8_7 | ~spl8_62 | ~spl8_65)),
% 0.21/0.52    inference(subsumption_resolution,[],[f728,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl8_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl8_4 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f728,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | (~spl8_7 | ~spl8_62 | ~spl8_65)),
% 0.21/0.52    inference(forward_demodulation,[],[f717,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl8_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl8_7 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f717,plain,(
% 0.21/0.52    ( ! [X20] : (sK0 = k4_xboole_0(k1_xboole_0,X20)) ) | (~spl8_62 | ~spl8_65)),
% 0.21/0.52    inference(resolution,[],[f706,f628])).
% 0.21/0.52  fof(f628,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) ) | ~spl8_62),
% 0.21/0.52    inference(avatar_component_clause,[],[f627])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    spl8_62 <=> ! [X6] : ~r2_hidden(X6,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 0.21/0.52  fof(f706,plain,(
% 0.21/0.52    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,sK0),X3) | sK0 = k4_xboole_0(X3,X4)) ) | ~spl8_65),
% 0.21/0.52    inference(avatar_component_clause,[],[f705])).
% 0.21/0.52  fof(f705,plain,(
% 0.21/0.52    spl8_65 <=> ! [X3,X4] : (sK0 = k4_xboole_0(X3,X4) | r2_hidden(sK2(X3,X4,sK0),X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).
% 0.21/0.52  fof(f707,plain,(
% 0.21/0.52    spl8_64 | spl8_65 | ~spl8_5 | ~spl8_34 | ~spl8_62),
% 0.21/0.52    inference(avatar_split_clause,[],[f695,f627,f299,f50,f705,f702])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    spl8_34 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2 | ~r2_hidden(X3,X4) | r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.52  fof(f695,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (sK0 = k4_xboole_0(X3,X4) | ~r2_hidden(X5,sK1) | r2_hidden(sK2(X3,X4,sK0),X3)) ) | (~spl8_5 | ~spl8_34 | ~spl8_62)),
% 0.21/0.52    inference(subsumption_resolution,[],[f683,f628])).
% 0.21/0.52  fof(f683,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(sK2(X3,X4,sK0),X5),k1_xboole_0) | sK0 = k4_xboole_0(X3,X4) | ~r2_hidden(X5,sK1) | r2_hidden(sK2(X3,X4,sK0),X3)) ) | (~spl8_5 | ~spl8_34)),
% 0.21/0.52    inference(superposition,[],[f300,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4)) | k4_xboole_0(X0,X1) = X2 | ~r2_hidden(X3,X4) | r2_hidden(sK2(X0,X1,X2),X0)) ) | ~spl8_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f299])).
% 0.21/0.52  fof(f663,plain,(
% 0.21/0.52    spl8_1 | ~spl8_18 | ~spl8_62),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f644])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    $false | (spl8_1 | ~spl8_18 | ~spl8_62)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f37,f628,f628,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl8_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl8_18 <=> ! [X1,X0,X2] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f629,plain,(
% 0.21/0.52    spl8_62 | ~spl8_52 | ~spl8_60),
% 0.21/0.52    inference(avatar_split_clause,[],[f619,f606,f540,f627])).
% 0.21/0.52  fof(f540,plain,(
% 0.21/0.52    spl8_52 <=> ! [X1,X0] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(sK5(k1_xboole_0,X0,X1),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.21/0.52  fof(f606,plain,(
% 0.21/0.52    spl8_60 <=> ! [X1,X0] : (~r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 0.21/0.52  fof(f619,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) ) | (~spl8_52 | ~spl8_60)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f618])).
% 0.21/0.52  fof(f618,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) ) | (~spl8_52 | ~spl8_60)),
% 0.21/0.52    inference(resolution,[],[f607,f541])).
% 0.21/0.52  fof(f541,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_52),
% 0.21/0.52    inference(avatar_component_clause,[],[f540])).
% 0.21/0.52  fof(f607,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_60),
% 0.21/0.52    inference(avatar_component_clause,[],[f606])).
% 0.21/0.52  fof(f608,plain,(
% 0.21/0.52    spl8_60 | ~spl8_7 | ~spl8_57),
% 0.21/0.52    inference(avatar_split_clause,[],[f598,f589,f61,f606])).
% 0.21/0.52  fof(f589,plain,(
% 0.21/0.52    spl8_57 <=> ! [X9,X7,X8] : (~r2_hidden(X7,k1_xboole_0) | ~r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 0.21/0.52  fof(f598,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl8_7 | ~spl8_57)),
% 0.21/0.52    inference(superposition,[],[f590,f62])).
% 0.21/0.52  fof(f590,plain,(
% 0.21/0.52    ( ! [X8,X7,X9] : (~r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8)) | ~r2_hidden(X7,k1_xboole_0)) ) | ~spl8_57),
% 0.21/0.52    inference(avatar_component_clause,[],[f589])).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    spl8_57 | ~spl8_8 | ~spl8_52),
% 0.21/0.52    inference(avatar_split_clause,[],[f558,f540,f65,f589])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl8_8 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f558,plain,(
% 0.21/0.52    ( ! [X8,X7,X9] : (~r2_hidden(X7,k1_xboole_0) | ~r2_hidden(sK5(k1_xboole_0,X8,X7),k4_xboole_0(X9,X8))) ) | (~spl8_8 | ~spl8_52)),
% 0.21/0.52    inference(resolution,[],[f541,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) ) | ~spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f542,plain,(
% 0.21/0.52    spl8_52 | ~spl8_11 | ~spl8_45),
% 0.21/0.52    inference(avatar_split_clause,[],[f452,f442,f78,f540])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl8_11 <=> ! [X1,X3,X0] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.52  fof(f442,plain,(
% 0.21/0.52    spl8_45 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.52  fof(f452,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(sK5(k1_xboole_0,X0,X1),X0)) ) | (~spl8_11 | ~spl8_45)),
% 0.21/0.52    inference(superposition,[],[f79,f443])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl8_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f442])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK5(X0,X1,X3),X1)) ) | ~spl8_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    spl8_47 | ~spl8_38 | ~spl8_43),
% 0.21/0.52    inference(avatar_split_clause,[],[f417,f399,f335,f475])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    spl8_38 <=> ! [X1,X0] : (k2_zfmisc_1(k1_xboole_0,X0) = X1 | r2_hidden(sK3(k1_xboole_0,X0,X1),X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    spl8_43 <=> ! [X1,X0] : (~r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0) | k2_zfmisc_1(k1_xboole_0,X1) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.21/0.52  fof(f417,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | r2_hidden(sK3(k1_xboole_0,X0,X1),X1)) ) | (~spl8_38 | ~spl8_43)),
% 0.21/0.52    inference(backward_demodulation,[],[f336,f415])).
% 0.21/0.52  fof(f415,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | (~spl8_38 | ~spl8_43)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f414])).
% 0.21/0.52  fof(f414,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | (~spl8_38 | ~spl8_43)),
% 0.21/0.52    inference(resolution,[],[f400,f336])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0) | k2_zfmisc_1(k1_xboole_0,X1) = X0) ) | ~spl8_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f399])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(k1_xboole_0,X0,X1),X1) | k2_zfmisc_1(k1_xboole_0,X0) = X1) ) | ~spl8_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f335])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    spl8_3 | ~spl8_45),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f449])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    $false | (spl8_3 | ~spl8_45)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f44,f443])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f444,plain,(
% 0.21/0.52    spl8_45 | ~spl8_38 | ~spl8_43),
% 0.21/0.52    inference(avatar_split_clause,[],[f415,f399,f335,f442])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    spl8_43 | ~spl8_7 | ~spl8_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f379,f372,f61,f399])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    spl8_40 <=> ! [X9,X7,X8] : (k2_zfmisc_1(k1_xboole_0,X7) = X8 | ~r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(k1_xboole_0,X1,X0),k1_xboole_0) | k2_zfmisc_1(k1_xboole_0,X1) = X0) ) | (~spl8_7 | ~spl8_40)),
% 0.21/0.52    inference(superposition,[],[f373,f62])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    ( ! [X8,X7,X9] : (~r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8)) | k2_zfmisc_1(k1_xboole_0,X7) = X8) ) | ~spl8_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f372])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    spl8_40 | ~spl8_8 | ~spl8_38),
% 0.21/0.52    inference(avatar_split_clause,[],[f346,f335,f65,f372])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ( ! [X8,X7,X9] : (k2_zfmisc_1(k1_xboole_0,X7) = X8 | ~r2_hidden(sK3(k1_xboole_0,X7,X8),k4_xboole_0(X9,X8))) ) | (~spl8_8 | ~spl8_38)),
% 0.21/0.52    inference(resolution,[],[f336,f66])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    spl8_38 | ~spl8_17 | ~spl8_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f319,f309,f102,f335])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl8_17 <=> ! [X1,X0,X2] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.52  % (13749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl8_35 <=> ! [X1,X0,X2] : (~r2_hidden(sK6(X0,X1,X2),k1_xboole_0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X0) = X1 | r2_hidden(sK3(k1_xboole_0,X0,X1),X1)) ) | (~spl8_17 | ~spl8_35)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f316])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X0) = X1 | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) | r2_hidden(sK3(k1_xboole_0,X0,X1),X1) | k2_zfmisc_1(k1_xboole_0,X0) = X1) ) | (~spl8_17 | ~spl8_35)),
% 0.21/0.52    inference(resolution,[],[f310,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl8_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),k1_xboole_0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) ) | ~spl8_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f309])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    spl8_35 | ~spl8_7 | ~spl8_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f177,f170,f61,f309])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl8_26 <=> ! [X9,X11,X10,X12] : (r2_hidden(sK3(X9,X10,X11),X11) | k2_zfmisc_1(X9,X10) = X11 | ~r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),k1_xboole_0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) ) | (~spl8_7 | ~spl8_26)),
% 0.21/0.52    inference(superposition,[],[f171,f62])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (~r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9)) | k2_zfmisc_1(X9,X10) = X11 | r2_hidden(sK3(X9,X10,X11),X11)) ) | ~spl8_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f170])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    spl8_34 | ~spl8_13 | ~spl8_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f109,f94,f86,f299])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl8_13 <=> ! [X1,X5,X0,X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl8_15 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2 | ~r2_hidden(X3,X4) | r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),k2_zfmisc_1(X2,X4))) ) | (~spl8_13 | ~spl8_15)),
% 0.21/0.52    inference(resolution,[],[f95,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) ) | ~spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl8_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl8_26 | ~spl8_8 | ~spl8_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f102,f65,f170])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (r2_hidden(sK3(X9,X10,X11),X11) | k2_zfmisc_1(X9,X10) = X11 | ~r2_hidden(sK6(X9,X10,X11),k4_xboole_0(X12,X9))) ) | (~spl8_8 | ~spl8_17)),
% 0.21/0.52    inference(resolution,[],[f103,f66])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl8_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f106])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl8_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f102])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl8_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f12,f94])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl8_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f86])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl8_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl8_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f10,f61])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl8_5 | spl8_2 | spl8_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f9,f46,f39,f50])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~spl8_3 | ~spl8_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f46,f43])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.52    inference(inner_rewriting,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~spl8_1 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f39,f36])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.52    inference(inner_rewriting,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (13752)------------------------------
% 0.21/0.52  % (13752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13752)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (13752)Memory used [KB]: 11385
% 0.21/0.52  % (13752)Time elapsed: 0.100 s
% 0.21/0.52  % (13752)------------------------------
% 0.21/0.52  % (13752)------------------------------
% 0.21/0.52  % (13753)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (13742)Success in time 0.158 s
%------------------------------------------------------------------------------
