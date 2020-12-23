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
% DateTime   : Thu Dec  3 13:04:09 EST 2020

% Result     : Theorem 3.56s
% Output     : Refutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  312 ( 513 expanded)
%              Number of leaves         :   85 ( 246 expanded)
%              Depth                    :    9
%              Number of atoms          :  966 (1603 expanded)
%              Number of equality atoms :  258 ( 435 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2941,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f130,f135,f140,f145,f149,f153,f162,f167,f171,f175,f179,f183,f195,f199,f205,f214,f224,f228,f238,f242,f251,f255,f274,f283,f287,f291,f321,f325,f384,f388,f392,f422,f427,f440,f488,f502,f546,f564,f578,f606,f656,f871,f1073,f1244,f1264,f1392,f1492,f1504,f1663,f1775,f1780,f2031,f2108,f2321,f2389,f2485,f2673,f2884,f2936])).

fof(f2936,plain,
    ( spl5_2
    | ~ spl5_68
    | ~ spl5_209
    | ~ spl5_232 ),
    inference(avatar_contradiction_clause,[],[f2935])).

fof(f2935,plain,
    ( $false
    | spl5_2
    | ~ spl5_68
    | ~ spl5_209
    | ~ spl5_232 ),
    inference(subsumption_resolution,[],[f129,f2931])).

fof(f2931,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_68
    | ~ spl5_209
    | ~ spl5_232 ),
    inference(unit_resulting_resolution,[],[f577,f2883,f2388])).

fof(f2388,plain,
    ( ! [X12,X13,X11] :
        ( ~ v1_funct_2(k1_xboole_0,X13,X11)
        | ~ r2_hidden(X12,X13)
        | k1_xboole_0 = X11 )
    | ~ spl5_209 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2387,plain,
    ( spl5_209
  <=> ! [X11,X13,X12] :
        ( k1_xboole_0 = X11
        | ~ r2_hidden(X12,X13)
        | ~ v1_funct_2(k1_xboole_0,X13,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f2883,plain,
    ( v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | ~ spl5_232 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f2881,plain,
    ( spl5_232
  <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f577,plain,
    ( ! [X0] : r2_hidden(X0,k1_tarski(X0))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl5_68
  <=> ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f129,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2884,plain,
    ( spl5_232
    | ~ spl5_3
    | ~ spl5_223 ),
    inference(avatar_split_clause,[],[f2778,f2670,f132,f2881])).

fof(f132,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2670,plain,
    ( spl5_223
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f2778,plain,
    ( v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | ~ spl5_3
    | ~ spl5_223 ),
    inference(superposition,[],[f134,f2672])).

fof(f2672,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_223 ),
    inference(avatar_component_clause,[],[f2670])).

fof(f134,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f2673,plain,
    ( spl5_223
    | ~ spl5_26
    | ~ spl5_33
    | ~ spl5_213 ),
    inference(avatar_split_clause,[],[f2570,f2482,f280,f240,f2670])).

fof(f240,plain,
    ( spl5_26
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f280,plain,
    ( spl5_33
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f2482,plain,
    ( spl5_213
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f2570,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_26
    | ~ spl5_33
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f282,f2484,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f240])).

fof(f2484,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_213 ),
    inference(avatar_component_clause,[],[f2482])).

fof(f282,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f280])).

fof(f2485,plain,
    ( spl5_213
    | ~ spl5_139
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f2374,f2318,f1501,f2482])).

fof(f1501,plain,
    ( spl5_139
  <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f2318,plain,
    ( spl5_204
  <=> k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f2374,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_139
    | ~ spl5_204 ),
    inference(superposition,[],[f2320,f1503])).

fof(f1503,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f2320,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f2318])).

fof(f2389,plain,
    ( spl5_209
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_21
    | ~ spl5_37
    | ~ spl5_114
    | ~ spl5_137
    | ~ spl5_163 ),
    inference(avatar_split_clause,[],[f1788,f1778,f1489,f1071,f319,f211,f169,f164,f159,f2387])).

fof(f159,plain,
    ( spl5_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f164,plain,
    ( spl5_10
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f169,plain,
    ( spl5_11
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f211,plain,
    ( spl5_21
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f319,plain,
    ( spl5_37
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1071,plain,
    ( spl5_114
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X3,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1489,plain,
    ( spl5_137
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f1778,plain,
    ( spl5_163
  <=> ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f1788,plain,
    ( ! [X12,X13,X11] :
        ( k1_xboole_0 = X11
        | ~ r2_hidden(X12,X13)
        | ~ v1_funct_2(k1_xboole_0,X13,X11) )
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_21
    | ~ spl5_37
    | ~ spl5_114
    | ~ spl5_137
    | ~ spl5_163 ),
    inference(subsumption_resolution,[],[f1494,f1786])).

fof(f1786,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_21
    | ~ spl5_37
    | ~ spl5_163 ),
    inference(forward_demodulation,[],[f1781,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1781,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl5_21
    | ~ spl5_37
    | ~ spl5_163 ),
    inference(unit_resulting_resolution,[],[f213,f1779,f320])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1779,plain,
    ( ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
    | ~ spl5_163 ),
    inference(avatar_component_clause,[],[f1778])).

fof(f213,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1494,plain,
    ( ! [X12,X13,X11] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X12),k1_xboole_0)
        | k1_xboole_0 = X11
        | ~ r2_hidden(X12,X13)
        | ~ v1_funct_2(k1_xboole_0,X13,X11) )
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_114
    | ~ spl5_137 ),
    inference(subsumption_resolution,[],[f1083,f1491])).

fof(f1491,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f1083,plain,
    ( ! [X12,X13,X11] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X12),k1_xboole_0)
        | k1_xboole_0 = X11
        | ~ r2_hidden(X12,X13)
        | ~ v1_funct_2(k1_xboole_0,X13,X11)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_114 ),
    inference(forward_demodulation,[],[f1078,f166])).

fof(f166,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1078,plain,
    ( ! [X12,X13,X11] :
        ( k1_xboole_0 = X11
        | ~ r2_hidden(X12,X13)
        | r2_hidden(k1_funct_1(k1_xboole_0,X12),k2_relat_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,X13,X11)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_11
    | ~ spl5_114 ),
    inference(resolution,[],[f1072,f170])).

fof(f170,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1072,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X3,X0)
        | r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f2321,plain,
    ( spl5_204
    | ~ spl5_33
    | ~ spl5_38
    | spl5_191 ),
    inference(avatar_split_clause,[],[f2191,f2105,f323,f280,f2318])).

fof(f323,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_relat_1(X1))
        | k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f2105,plain,
    ( spl5_191
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f2191,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ spl5_33
    | ~ spl5_38
    | spl5_191 ),
    inference(unit_resulting_resolution,[],[f282,f2107,f324])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f323])).

fof(f2107,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl5_191 ),
    inference(avatar_component_clause,[],[f2105])).

fof(f2108,plain,
    ( ~ spl5_191
    | ~ spl5_56
    | spl5_123
    | ~ spl5_185 ),
    inference(avatar_split_clause,[],[f2039,f2029,f1241,f499,f2105])).

fof(f499,plain,
    ( spl5_56
  <=> r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1241,plain,
    ( spl5_123
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f2029,plain,
    ( spl5_185
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = X1
        | ~ r1_tarski(X1,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f2039,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_56
    | spl5_123
    | ~ spl5_185 ),
    inference(unit_resulting_resolution,[],[f1243,f501,f2030])).

fof(f2030,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tarski(X0))
        | k1_tarski(X0) = X1
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_185 ),
    inference(avatar_component_clause,[],[f2029])).

fof(f501,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f499])).

fof(f1243,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | spl5_123 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f2031,plain,
    ( spl5_185
    | ~ spl5_28
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f660,f654,f249,f2029])).

fof(f249,plain,
    ( spl5_28
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f654,plain,
    ( spl5_76
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f660,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = X1
        | ~ r1_tarski(X1,k1_tarski(X0)) )
    | ~ spl5_28
    | ~ spl5_76 ),
    inference(resolution,[],[f655,f250])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f249])).

fof(f655,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f654])).

fof(f1780,plain,
    ( spl5_163
    | ~ spl5_159
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1776,f1773,f1661,f1778])).

fof(f1661,plain,
    ( spl5_159
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1773,plain,
    ( spl5_162
  <=> ! [X0] : k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1776,plain,
    ( ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
    | ~ spl5_159
    | ~ spl5_162 ),
    inference(forward_demodulation,[],[f1774,f1662])).

fof(f1662,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl5_159 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f1774,plain,
    ( ! [X0] : k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))
    | ~ spl5_162 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1775,plain,
    ( spl5_162
    | ~ spl5_21
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f516,f272,f211,f1773])).

fof(f272,plain,
    ( spl5_31
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f516,plain,
    ( ! [X0] : k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))
    | ~ spl5_21
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f213,f273])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f272])).

fof(f1663,plain,
    ( spl5_159
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_65
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f880,f869,f562,f211,f164,f1661])).

fof(f562,plain,
    ( spl5_65
  <=> ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f869,plain,
    ( spl5_98
  <=> ! [X1,X0] :
        ( k2_relat_1(X0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f880,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_65
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f872,f166])).

fof(f872,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl5_21
    | ~ spl5_65
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f563,f213,f870])).

fof(f870,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(X0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f869])).

fof(f563,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f562])).

fof(f1504,plain,
    ( spl5_139
    | ~ spl5_124
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f1393,f1389,f1262,f1501])).

fof(f1262,plain,
    ( spl5_124
  <=> ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1389,plain,
    ( spl5_132
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f1393,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl5_124
    | ~ spl5_132 ),
    inference(superposition,[],[f1391,f1263])).

fof(f1263,plain,
    ( ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f1262])).

fof(f1391,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f1389])).

fof(f1492,plain,
    ( spl5_137
    | ~ spl5_7
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f609,f603,f151,f1489])).

fof(f151,plain,
    ( spl5_7
  <=> ! [X0] : v1_funct_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f603,plain,
    ( spl5_70
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f609,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_70 ),
    inference(superposition,[],[f152,f605])).

fof(f605,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f603])).

fof(f152,plain,
    ( ! [X0] : v1_funct_1(sK3(X0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1392,plain,
    ( spl5_132
    | ~ spl5_33
    | ~ spl5_48
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f873,f869,f424,f280,f1389])).

fof(f424,plain,
    ( spl5_48
  <=> v4_relat_1(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f873,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ spl5_33
    | ~ spl5_48
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f426,f282,f870])).

fof(f426,plain,
    ( v4_relat_1(sK2,k1_tarski(sK0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f424])).

fof(f1264,plain,
    ( spl5_124
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f336,f280,f272,f1262])).

fof(f336,plain,
    ( ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f282,f273])).

fof(f1244,plain,
    ( ~ spl5_123
    | ~ spl5_1
    | ~ spl5_33
    | ~ spl5_47
    | spl5_63 ),
    inference(avatar_split_clause,[],[f1223,f543,f420,f280,f122,f1241])).

fof(f122,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f420,plain,
    ( spl5_47
  <=> ! [X1,X0] :
        ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
        | k1_tarski(X0) != k1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f543,plain,
    ( spl5_63
  <=> k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f1223,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_33
    | ~ spl5_47
    | spl5_63 ),
    inference(unit_resulting_resolution,[],[f282,f124,f545,f421])).

fof(f421,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) != k1_relat_1(X1)
        | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f420])).

fof(f545,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl5_63 ),
    inference(avatar_component_clause,[],[f543])).

fof(f124,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1073,plain,
    ( spl5_114
    | ~ spl5_43
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f443,f438,f386,f1071])).

fof(f386,plain,
    ( spl5_43
  <=> ! [X1,X0,X2] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f438,plain,
    ( spl5_50
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ v1_funct_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f443,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X3,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
    | ~ spl5_43
    | ~ spl5_50 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X3,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_43
    | ~ spl5_50 ),
    inference(superposition,[],[f439,f387])).

fof(f387,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f386])).

fof(f439,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ v1_funct_1(X3) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f438])).

fof(f871,plain,
    ( spl5_98
    | ~ spl5_34
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f344,f289,f285,f869])).

fof(f285,plain,
    ( spl5_34
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f289,plain,
    ( spl5_35
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(X0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl5_34
    | ~ spl5_35 ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(X0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_34
    | ~ spl5_35 ),
    inference(superposition,[],[f286,f290])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f289])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f285])).

fof(f656,plain,
    ( spl5_76
    | ~ spl5_19
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f262,f222,f203,f654])).

fof(f203,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f222,plain,
    ( spl5_23
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) )
    | ~ spl5_19
    | ~ spl5_23 ),
    inference(resolution,[],[f223,f204])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f222])).

fof(f606,plain,
    ( spl5_70
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f296,f236,f177,f147,f603])).

fof(f147,plain,
    ( spl5_6
  <=> ! [X0] : v1_relat_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f177,plain,
    ( spl5_13
  <=> ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f236,plain,
    ( spl5_25
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f296,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f148,f178,f237])).

fof(f237,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f178,plain,
    ( ! [X0] : k1_relat_1(sK3(X0)) = X0
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f148,plain,
    ( ! [X0] : v1_relat_1(sK3(X0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f578,plain,
    ( spl5_68
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f215,f197,f193,f576])).

fof(f193,plain,
    ( spl5_17
  <=> ! [X1,X4] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f197,plain,
    ( spl5_18
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f215,plain,
    ( ! [X0] : r2_hidden(X0,k1_tarski(X0))
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(superposition,[],[f194,f198])).

fof(f198,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f194,plain,
    ( ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f564,plain,
    ( spl5_65
    | ~ spl5_11
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f303,f253,f169,f562])).

fof(f253,plain,
    ( spl5_29
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f303,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl5_11
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f170,f254])).

fof(f254,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f546,plain,
    ( ~ spl5_4
    | ~ spl5_63
    | spl5_5
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f406,f386,f142,f543,f137])).

fof(f137,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,
    ( spl5_5
  <=> k2_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f406,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | spl5_5
    | ~ spl5_43 ),
    inference(superposition,[],[f144,f387])).

fof(f144,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f502,plain,
    ( spl5_56
    | ~ spl5_19
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f489,f485,f203,f499])).

fof(f485,plain,
    ( spl5_54
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f489,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ spl5_19
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f487,f204])).

fof(f487,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0)))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f485])).

fof(f488,plain,
    ( spl5_54
    | ~ spl5_4
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f418,f390,f382,f137,f485])).

fof(f382,plain,
    ( spl5_42
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f390,plain,
    ( spl5_44
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f418,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0)))
    | ~ spl5_4
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f408,f401])).

fof(f401,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ spl5_4
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f139,f383])).

fof(f383,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f382])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f408,plain,
    ( m1_subset_1(k1_relset_1(k1_tarski(sK0),sK1,sK2),k1_zfmisc_1(k1_tarski(sK0)))
    | ~ spl5_4
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f139,f391])).

fof(f391,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f390])).

fof(f440,plain,(
    spl5_50 ),
    inference(avatar_split_clause,[],[f109,f438])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f427,plain,
    ( spl5_48
    | ~ spl5_4
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f302,f253,f137,f424])).

fof(f302,plain,
    ( v4_relat_1(sK2,k1_tarski(sK0))
    | ~ spl5_4
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f139,f254])).

fof(f422,plain,(
    spl5_47 ),
    inference(avatar_split_clause,[],[f86,f420])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f392,plain,(
    spl5_44 ),
    inference(avatar_split_clause,[],[f99,f390])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f388,plain,(
    spl5_43 ),
    inference(avatar_split_clause,[],[f98,f386])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f384,plain,(
    spl5_42 ),
    inference(avatar_split_clause,[],[f97,f382])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f325,plain,(
    spl5_38 ),
    inference(avatar_split_clause,[],[f84,f323])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f321,plain,(
    spl5_37 ),
    inference(avatar_split_clause,[],[f83,f319])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f291,plain,(
    spl5_35 ),
    inference(avatar_split_clause,[],[f87,f289])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f287,plain,(
    spl5_34 ),
    inference(avatar_split_clause,[],[f82,f285])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f283,plain,
    ( spl5_33
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f263,f226,f137,f280])).

fof(f226,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f263,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f139,f227])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f274,plain,(
    spl5_31 ),
    inference(avatar_split_clause,[],[f75,f272])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f255,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f100,f253])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f251,plain,(
    spl5_28 ),
    inference(avatar_split_clause,[],[f90,f249])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,(
    spl5_26 ),
    inference(avatar_split_clause,[],[f74,f240])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f238,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f73,f236])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f228,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f96,f226])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f224,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f85,f222])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f214,plain,
    ( spl5_21
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f200,f181,f173,f211])).

fof(f173,plain,
    ( spl5_12
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f181,plain,
    ( spl5_14
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f200,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(superposition,[],[f174,f182])).

fof(f182,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f181])).

fof(f174,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f205,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f91,f203])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f199,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f72,f197])).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f195,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f117,f193])).

fof(f117,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f183,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f112,f181])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f179,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f78,f177])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = k1_tarski(X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_tarski(X2) = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k1_tarski(X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_tarski(X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(f175,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f80,f173])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f171,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f71,f169])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f167,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f70,f164])).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f162,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f69,f159])).

fof(f69,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f153,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f77,f151])).

fof(f77,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f149,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f76,f147])).

fof(f76,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f145,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f68,f142])).

fof(f68,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f140,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f66,f137])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f135,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f65,f132])).

fof(f65,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f130,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f127])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f125,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f64,f122])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19328)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (19320)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (19310)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (19311)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (19309)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (19304)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (19317)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (19307)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (19331)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (19330)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (19318)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (19308)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (19305)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (19312)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (19314)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (19334)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (19306)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (19332)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (19324)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (19315)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (19322)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (19323)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (19327)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (19329)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (19305)Refutation not found, incomplete strategy% (19305)------------------------------
% 0.22/0.55  % (19305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (19325)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (19316)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (19321)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (19305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (19305)Memory used [KB]: 1663
% 0.22/0.56  % (19305)Time elapsed: 0.134 s
% 0.22/0.56  % (19305)------------------------------
% 0.22/0.56  % (19305)------------------------------
% 1.54/0.56  % (19326)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.56  % (19313)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.56  % (19334)Refutation not found, incomplete strategy% (19334)------------------------------
% 1.54/0.56  % (19334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (19334)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (19334)Memory used [KB]: 1663
% 1.54/0.56  % (19334)Time elapsed: 0.146 s
% 1.54/0.56  % (19334)------------------------------
% 1.54/0.56  % (19334)------------------------------
% 1.54/0.57  % (19318)Refutation not found, incomplete strategy% (19318)------------------------------
% 1.54/0.57  % (19318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (19318)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (19318)Memory used [KB]: 1791
% 1.54/0.57  % (19318)Time elapsed: 0.151 s
% 1.54/0.57  % (19318)------------------------------
% 1.54/0.57  % (19318)------------------------------
% 1.54/0.57  % (19333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.57  % (19321)Refutation not found, incomplete strategy% (19321)------------------------------
% 1.54/0.57  % (19321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (19321)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (19321)Memory used [KB]: 10746
% 1.54/0.57  % (19321)Time elapsed: 0.158 s
% 1.54/0.57  % (19321)------------------------------
% 1.54/0.57  % (19321)------------------------------
% 1.54/0.57  % (19333)Refutation not found, incomplete strategy% (19333)------------------------------
% 1.54/0.57  % (19333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (19314)Refutation not found, incomplete strategy% (19314)------------------------------
% 1.54/0.57  % (19314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (19314)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (19314)Memory used [KB]: 10874
% 1.68/0.58  % (19314)Time elapsed: 0.158 s
% 1.68/0.58  % (19314)------------------------------
% 1.68/0.58  % (19314)------------------------------
% 1.68/0.58  % (19333)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (19333)Memory used [KB]: 10874
% 1.68/0.58  % (19333)Time elapsed: 0.144 s
% 1.68/0.58  % (19333)------------------------------
% 1.68/0.58  % (19333)------------------------------
% 2.15/0.69  % (19346)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.15/0.70  % (19351)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.15/0.70  % (19349)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.15/0.71  % (19348)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.15/0.71  % (19307)Refutation not found, incomplete strategy% (19307)------------------------------
% 2.15/0.71  % (19307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.71  % (19307)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.71  
% 2.15/0.71  % (19307)Memory used [KB]: 6140
% 2.15/0.71  % (19307)Time elapsed: 0.295 s
% 2.15/0.71  % (19307)------------------------------
% 2.15/0.71  % (19307)------------------------------
% 2.62/0.72  % (19350)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.62/0.74  % (19347)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.91/0.82  % (19329)Time limit reached!
% 2.91/0.82  % (19329)------------------------------
% 2.91/0.82  % (19329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.82  % (19329)Termination reason: Time limit
% 2.91/0.82  % (19329)Termination phase: Saturation
% 2.91/0.82  
% 2.91/0.82  % (19329)Memory used [KB]: 12409
% 2.91/0.82  % (19329)Time elapsed: 0.400 s
% 2.91/0.82  % (19329)------------------------------
% 2.91/0.82  % (19329)------------------------------
% 3.37/0.86  % (19306)Time limit reached!
% 3.37/0.86  % (19306)------------------------------
% 3.37/0.86  % (19306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.86  % (19306)Termination reason: Time limit
% 3.37/0.86  % (19306)Termination phase: Saturation
% 3.37/0.86  
% 3.37/0.86  % (19306)Memory used [KB]: 6652
% 3.37/0.86  % (19306)Time elapsed: 0.400 s
% 3.37/0.86  % (19306)------------------------------
% 3.37/0.86  % (19306)------------------------------
% 3.56/0.88  % (19346)Refutation found. Thanks to Tanya!
% 3.56/0.88  % SZS status Theorem for theBenchmark
% 3.56/0.88  % SZS output start Proof for theBenchmark
% 3.56/0.88  fof(f2941,plain,(
% 3.56/0.88    $false),
% 3.56/0.88    inference(avatar_sat_refutation,[],[f125,f130,f135,f140,f145,f149,f153,f162,f167,f171,f175,f179,f183,f195,f199,f205,f214,f224,f228,f238,f242,f251,f255,f274,f283,f287,f291,f321,f325,f384,f388,f392,f422,f427,f440,f488,f502,f546,f564,f578,f606,f656,f871,f1073,f1244,f1264,f1392,f1492,f1504,f1663,f1775,f1780,f2031,f2108,f2321,f2389,f2485,f2673,f2884,f2936])).
% 3.56/0.88  fof(f2936,plain,(
% 3.56/0.88    spl5_2 | ~spl5_68 | ~spl5_209 | ~spl5_232),
% 3.56/0.88    inference(avatar_contradiction_clause,[],[f2935])).
% 3.56/0.88  fof(f2935,plain,(
% 3.56/0.88    $false | (spl5_2 | ~spl5_68 | ~spl5_209 | ~spl5_232)),
% 3.56/0.88    inference(subsumption_resolution,[],[f129,f2931])).
% 3.56/0.88  fof(f2931,plain,(
% 3.56/0.88    k1_xboole_0 = sK1 | (~spl5_68 | ~spl5_209 | ~spl5_232)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f577,f2883,f2388])).
% 3.56/0.88  fof(f2388,plain,(
% 3.56/0.88    ( ! [X12,X13,X11] : (~v1_funct_2(k1_xboole_0,X13,X11) | ~r2_hidden(X12,X13) | k1_xboole_0 = X11) ) | ~spl5_209),
% 3.56/0.88    inference(avatar_component_clause,[],[f2387])).
% 3.56/0.88  fof(f2387,plain,(
% 3.56/0.88    spl5_209 <=> ! [X11,X13,X12] : (k1_xboole_0 = X11 | ~r2_hidden(X12,X13) | ~v1_funct_2(k1_xboole_0,X13,X11))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).
% 3.56/0.88  fof(f2883,plain,(
% 3.56/0.88    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | ~spl5_232),
% 3.56/0.88    inference(avatar_component_clause,[],[f2881])).
% 3.56/0.88  fof(f2881,plain,(
% 3.56/0.88    spl5_232 <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).
% 3.56/0.88  fof(f577,plain,(
% 3.56/0.88    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) ) | ~spl5_68),
% 3.56/0.88    inference(avatar_component_clause,[],[f576])).
% 3.56/0.88  fof(f576,plain,(
% 3.56/0.88    spl5_68 <=> ! [X0] : r2_hidden(X0,k1_tarski(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 3.56/0.88  fof(f129,plain,(
% 3.56/0.88    k1_xboole_0 != sK1 | spl5_2),
% 3.56/0.88    inference(avatar_component_clause,[],[f127])).
% 3.56/0.88  fof(f127,plain,(
% 3.56/0.88    spl5_2 <=> k1_xboole_0 = sK1),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.56/0.88  fof(f2884,plain,(
% 3.56/0.88    spl5_232 | ~spl5_3 | ~spl5_223),
% 3.56/0.88    inference(avatar_split_clause,[],[f2778,f2670,f132,f2881])).
% 3.56/0.88  fof(f132,plain,(
% 3.56/0.88    spl5_3 <=> v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.56/0.88  fof(f2670,plain,(
% 3.56/0.88    spl5_223 <=> k1_xboole_0 = sK2),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).
% 3.56/0.88  fof(f2778,plain,(
% 3.56/0.88    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | (~spl5_3 | ~spl5_223)),
% 3.56/0.88    inference(superposition,[],[f134,f2672])).
% 3.56/0.88  fof(f2672,plain,(
% 3.56/0.88    k1_xboole_0 = sK2 | ~spl5_223),
% 3.56/0.88    inference(avatar_component_clause,[],[f2670])).
% 3.56/0.88  fof(f134,plain,(
% 3.56/0.88    v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~spl5_3),
% 3.56/0.88    inference(avatar_component_clause,[],[f132])).
% 3.56/0.88  fof(f2673,plain,(
% 3.56/0.88    spl5_223 | ~spl5_26 | ~spl5_33 | ~spl5_213),
% 3.56/0.88    inference(avatar_split_clause,[],[f2570,f2482,f280,f240,f2670])).
% 3.56/0.88  fof(f240,plain,(
% 3.56/0.88    spl5_26 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 3.56/0.88  fof(f280,plain,(
% 3.56/0.88    spl5_33 <=> v1_relat_1(sK2)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 3.56/0.88  fof(f2482,plain,(
% 3.56/0.88    spl5_213 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).
% 3.56/0.88  fof(f2570,plain,(
% 3.56/0.88    k1_xboole_0 = sK2 | (~spl5_26 | ~spl5_33 | ~spl5_213)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f282,f2484,f241])).
% 3.56/0.88  fof(f241,plain,(
% 3.56/0.88    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl5_26),
% 3.56/0.88    inference(avatar_component_clause,[],[f240])).
% 3.56/0.88  fof(f2484,plain,(
% 3.56/0.88    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_213),
% 3.56/0.88    inference(avatar_component_clause,[],[f2482])).
% 3.56/0.88  fof(f282,plain,(
% 3.56/0.88    v1_relat_1(sK2) | ~spl5_33),
% 3.56/0.88    inference(avatar_component_clause,[],[f280])).
% 3.56/0.88  fof(f2485,plain,(
% 3.56/0.88    spl5_213 | ~spl5_139 | ~spl5_204),
% 3.56/0.88    inference(avatar_split_clause,[],[f2374,f2318,f1501,f2482])).
% 3.56/0.88  fof(f1501,plain,(
% 3.56/0.88    spl5_139 <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).
% 3.56/0.88  fof(f2318,plain,(
% 3.56/0.88    spl5_204 <=> k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).
% 3.56/0.88  fof(f2374,plain,(
% 3.56/0.88    k1_xboole_0 = k2_relat_1(sK2) | (~spl5_139 | ~spl5_204)),
% 3.56/0.88    inference(superposition,[],[f2320,f1503])).
% 3.56/0.88  fof(f1503,plain,(
% 3.56/0.88    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~spl5_139),
% 3.56/0.88    inference(avatar_component_clause,[],[f1501])).
% 3.56/0.88  fof(f2320,plain,(
% 3.56/0.88    k1_xboole_0 = k11_relat_1(sK2,sK0) | ~spl5_204),
% 3.56/0.88    inference(avatar_component_clause,[],[f2318])).
% 3.56/0.88  fof(f2389,plain,(
% 3.56/0.88    spl5_209 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_21 | ~spl5_37 | ~spl5_114 | ~spl5_137 | ~spl5_163),
% 3.56/0.88    inference(avatar_split_clause,[],[f1788,f1778,f1489,f1071,f319,f211,f169,f164,f159,f2387])).
% 3.56/0.88  fof(f159,plain,(
% 3.56/0.88    spl5_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.56/0.88  fof(f164,plain,(
% 3.56/0.88    spl5_10 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.56/0.88  fof(f169,plain,(
% 3.56/0.88    spl5_11 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.56/0.88  fof(f211,plain,(
% 3.56/0.88    spl5_21 <=> v1_relat_1(k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 3.56/0.88  fof(f319,plain,(
% 3.56/0.88    spl5_37 <=> ! [X1,X0] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 3.56/0.88  fof(f1071,plain,(
% 3.56/0.88    spl5_114 <=> ! [X1,X3,X0,X2] : (r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 3.56/0.88  fof(f1489,plain,(
% 3.56/0.88    spl5_137 <=> v1_funct_1(k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).
% 3.56/0.88  fof(f1778,plain,(
% 3.56/0.88    spl5_163 <=> ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).
% 3.56/0.88  fof(f1788,plain,(
% 3.56/0.88    ( ! [X12,X13,X11] : (k1_xboole_0 = X11 | ~r2_hidden(X12,X13) | ~v1_funct_2(k1_xboole_0,X13,X11)) ) | (~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_21 | ~spl5_37 | ~spl5_114 | ~spl5_137 | ~spl5_163)),
% 3.56/0.88    inference(subsumption_resolution,[],[f1494,f1786])).
% 3.56/0.88  fof(f1786,plain,(
% 3.56/0.88    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_9 | ~spl5_21 | ~spl5_37 | ~spl5_163)),
% 3.56/0.88    inference(forward_demodulation,[],[f1781,f161])).
% 3.56/0.88  fof(f161,plain,(
% 3.56/0.88    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_9),
% 3.56/0.88    inference(avatar_component_clause,[],[f159])).
% 3.56/0.88  fof(f1781,plain,(
% 3.56/0.88    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | (~spl5_21 | ~spl5_37 | ~spl5_163)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f213,f1779,f320])).
% 3.56/0.88  fof(f320,plain,(
% 3.56/0.88    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_37),
% 3.56/0.88    inference(avatar_component_clause,[],[f319])).
% 3.56/0.88  fof(f1779,plain,(
% 3.56/0.88    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) ) | ~spl5_163),
% 3.56/0.88    inference(avatar_component_clause,[],[f1778])).
% 3.56/0.88  fof(f213,plain,(
% 3.56/0.88    v1_relat_1(k1_xboole_0) | ~spl5_21),
% 3.56/0.88    inference(avatar_component_clause,[],[f211])).
% 3.56/0.88  fof(f1494,plain,(
% 3.56/0.88    ( ! [X12,X13,X11] : (r2_hidden(k1_funct_1(k1_xboole_0,X12),k1_xboole_0) | k1_xboole_0 = X11 | ~r2_hidden(X12,X13) | ~v1_funct_2(k1_xboole_0,X13,X11)) ) | (~spl5_10 | ~spl5_11 | ~spl5_114 | ~spl5_137)),
% 3.56/0.88    inference(subsumption_resolution,[],[f1083,f1491])).
% 3.56/0.88  fof(f1491,plain,(
% 3.56/0.88    v1_funct_1(k1_xboole_0) | ~spl5_137),
% 3.56/0.88    inference(avatar_component_clause,[],[f1489])).
% 3.56/0.88  fof(f1083,plain,(
% 3.56/0.88    ( ! [X12,X13,X11] : (r2_hidden(k1_funct_1(k1_xboole_0,X12),k1_xboole_0) | k1_xboole_0 = X11 | ~r2_hidden(X12,X13) | ~v1_funct_2(k1_xboole_0,X13,X11) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_10 | ~spl5_11 | ~spl5_114)),
% 3.56/0.88    inference(forward_demodulation,[],[f1078,f166])).
% 3.56/0.88  fof(f166,plain,(
% 3.56/0.88    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_10),
% 3.56/0.88    inference(avatar_component_clause,[],[f164])).
% 3.56/0.88  fof(f1078,plain,(
% 3.56/0.88    ( ! [X12,X13,X11] : (k1_xboole_0 = X11 | ~r2_hidden(X12,X13) | r2_hidden(k1_funct_1(k1_xboole_0,X12),k2_relat_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,X13,X11) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_11 | ~spl5_114)),
% 3.56/0.88    inference(resolution,[],[f1072,f170])).
% 3.56/0.88  fof(f170,plain,(
% 3.56/0.88    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_11),
% 3.56/0.88    inference(avatar_component_clause,[],[f169])).
% 3.56/0.88  fof(f1072,plain,(
% 3.56/0.88    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) ) | ~spl5_114),
% 3.56/0.88    inference(avatar_component_clause,[],[f1071])).
% 3.56/0.88  fof(f2321,plain,(
% 3.56/0.88    spl5_204 | ~spl5_33 | ~spl5_38 | spl5_191),
% 3.56/0.88    inference(avatar_split_clause,[],[f2191,f2105,f323,f280,f2318])).
% 3.56/0.88  fof(f323,plain,(
% 3.56/0.88    spl5_38 <=> ! [X1,X0] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 3.56/0.88  fof(f2105,plain,(
% 3.56/0.88    spl5_191 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).
% 3.56/0.88  fof(f2191,plain,(
% 3.56/0.88    k1_xboole_0 = k11_relat_1(sK2,sK0) | (~spl5_33 | ~spl5_38 | spl5_191)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f282,f2107,f324])).
% 3.56/0.88  fof(f324,plain,(
% 3.56/0.88    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_38),
% 3.56/0.88    inference(avatar_component_clause,[],[f323])).
% 3.56/0.88  fof(f2107,plain,(
% 3.56/0.88    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl5_191),
% 3.56/0.88    inference(avatar_component_clause,[],[f2105])).
% 3.56/0.88  fof(f2108,plain,(
% 3.56/0.88    ~spl5_191 | ~spl5_56 | spl5_123 | ~spl5_185),
% 3.56/0.88    inference(avatar_split_clause,[],[f2039,f2029,f1241,f499,f2105])).
% 3.56/0.88  fof(f499,plain,(
% 3.56/0.88    spl5_56 <=> r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 3.56/0.88  fof(f1241,plain,(
% 3.56/0.88    spl5_123 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 3.56/0.88  fof(f2029,plain,(
% 3.56/0.88    spl5_185 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_tarski(X0) = X1 | ~r1_tarski(X1,k1_tarski(X0)))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).
% 3.56/0.88  fof(f2039,plain,(
% 3.56/0.88    ~r2_hidden(sK0,k1_relat_1(sK2)) | (~spl5_56 | spl5_123 | ~spl5_185)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f1243,f501,f2030])).
% 3.56/0.88  fof(f2030,plain,(
% 3.56/0.88    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) ) | ~spl5_185),
% 3.56/0.88    inference(avatar_component_clause,[],[f2029])).
% 3.56/0.88  fof(f501,plain,(
% 3.56/0.88    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) | ~spl5_56),
% 3.56/0.88    inference(avatar_component_clause,[],[f499])).
% 3.56/0.88  fof(f1243,plain,(
% 3.56/0.88    k1_tarski(sK0) != k1_relat_1(sK2) | spl5_123),
% 3.56/0.88    inference(avatar_component_clause,[],[f1241])).
% 3.56/0.88  fof(f2031,plain,(
% 3.56/0.88    spl5_185 | ~spl5_28 | ~spl5_76),
% 3.56/0.88    inference(avatar_split_clause,[],[f660,f654,f249,f2029])).
% 3.56/0.88  fof(f249,plain,(
% 3.56/0.88    spl5_28 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 3.56/0.88  fof(f654,plain,(
% 3.56/0.88    spl5_76 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 3.56/0.88  fof(f660,plain,(
% 3.56/0.88    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = X1 | ~r1_tarski(X1,k1_tarski(X0))) ) | (~spl5_28 | ~spl5_76)),
% 3.56/0.88    inference(resolution,[],[f655,f250])).
% 3.56/0.88  fof(f250,plain,(
% 3.56/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl5_28),
% 3.56/0.88    inference(avatar_component_clause,[],[f249])).
% 3.56/0.88  fof(f655,plain,(
% 3.56/0.88    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl5_76),
% 3.56/0.88    inference(avatar_component_clause,[],[f654])).
% 3.56/0.88  fof(f1780,plain,(
% 3.56/0.88    spl5_163 | ~spl5_159 | ~spl5_162),
% 3.56/0.88    inference(avatar_split_clause,[],[f1776,f1773,f1661,f1778])).
% 3.56/0.88  fof(f1661,plain,(
% 3.56/0.88    spl5_159 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).
% 3.56/0.88  fof(f1773,plain,(
% 3.56/0.88    spl5_162 <=> ! [X0] : k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).
% 3.56/0.88  fof(f1776,plain,(
% 3.56/0.88    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) ) | (~spl5_159 | ~spl5_162)),
% 3.56/0.88    inference(forward_demodulation,[],[f1774,f1662])).
% 3.56/0.88  fof(f1662,plain,(
% 3.56/0.88    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl5_159),
% 3.56/0.88    inference(avatar_component_clause,[],[f1661])).
% 3.56/0.88  fof(f1774,plain,(
% 3.56/0.88    ( ! [X0] : (k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))) ) | ~spl5_162),
% 3.56/0.88    inference(avatar_component_clause,[],[f1773])).
% 3.56/0.88  fof(f1775,plain,(
% 3.56/0.88    spl5_162 | ~spl5_21 | ~spl5_31),
% 3.56/0.88    inference(avatar_split_clause,[],[f516,f272,f211,f1773])).
% 3.56/0.88  fof(f272,plain,(
% 3.56/0.88    spl5_31 <=> ! [X1,X0] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 3.56/0.88  fof(f516,plain,(
% 3.56/0.88    ( ! [X0] : (k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))) ) | (~spl5_21 | ~spl5_31)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f213,f273])).
% 3.56/0.88  fof(f273,plain,(
% 3.56/0.88    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl5_31),
% 3.56/0.88    inference(avatar_component_clause,[],[f272])).
% 3.56/0.88  fof(f1663,plain,(
% 3.56/0.88    spl5_159 | ~spl5_10 | ~spl5_21 | ~spl5_65 | ~spl5_98),
% 3.56/0.88    inference(avatar_split_clause,[],[f880,f869,f562,f211,f164,f1661])).
% 3.56/0.88  fof(f562,plain,(
% 3.56/0.88    spl5_65 <=> ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 3.56/0.88  fof(f869,plain,(
% 3.56/0.88    spl5_98 <=> ! [X1,X0] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 3.56/0.88  fof(f880,plain,(
% 3.56/0.88    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_21 | ~spl5_65 | ~spl5_98)),
% 3.56/0.88    inference(forward_demodulation,[],[f872,f166])).
% 3.56/0.88  fof(f872,plain,(
% 3.56/0.88    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl5_21 | ~spl5_65 | ~spl5_98)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f563,f213,f870])).
% 3.56/0.88  fof(f870,plain,(
% 3.56/0.88    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | ~spl5_98),
% 3.56/0.88    inference(avatar_component_clause,[],[f869])).
% 3.56/0.88  fof(f563,plain,(
% 3.56/0.88    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl5_65),
% 3.56/0.88    inference(avatar_component_clause,[],[f562])).
% 3.56/0.88  fof(f1504,plain,(
% 3.56/0.88    spl5_139 | ~spl5_124 | ~spl5_132),
% 3.56/0.88    inference(avatar_split_clause,[],[f1393,f1389,f1262,f1501])).
% 3.56/0.88  fof(f1262,plain,(
% 3.56/0.88    spl5_124 <=> ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 3.56/0.88  fof(f1389,plain,(
% 3.56/0.88    spl5_132 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).
% 3.56/0.88  fof(f1393,plain,(
% 3.56/0.88    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | (~spl5_124 | ~spl5_132)),
% 3.56/0.88    inference(superposition,[],[f1391,f1263])).
% 3.56/0.88  fof(f1263,plain,(
% 3.56/0.88    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))) ) | ~spl5_124),
% 3.56/0.88    inference(avatar_component_clause,[],[f1262])).
% 3.56/0.88  fof(f1391,plain,(
% 3.56/0.88    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~spl5_132),
% 3.56/0.88    inference(avatar_component_clause,[],[f1389])).
% 3.56/0.88  fof(f1492,plain,(
% 3.56/0.88    spl5_137 | ~spl5_7 | ~spl5_70),
% 3.56/0.88    inference(avatar_split_clause,[],[f609,f603,f151,f1489])).
% 3.56/0.88  fof(f151,plain,(
% 3.56/0.88    spl5_7 <=> ! [X0] : v1_funct_1(sK3(X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.56/0.88  fof(f603,plain,(
% 3.56/0.88    spl5_70 <=> k1_xboole_0 = sK3(k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 3.56/0.88  fof(f609,plain,(
% 3.56/0.88    v1_funct_1(k1_xboole_0) | (~spl5_7 | ~spl5_70)),
% 3.56/0.88    inference(superposition,[],[f152,f605])).
% 3.56/0.88  fof(f605,plain,(
% 3.56/0.88    k1_xboole_0 = sK3(k1_xboole_0) | ~spl5_70),
% 3.56/0.88    inference(avatar_component_clause,[],[f603])).
% 3.56/0.88  fof(f152,plain,(
% 3.56/0.88    ( ! [X0] : (v1_funct_1(sK3(X0))) ) | ~spl5_7),
% 3.56/0.88    inference(avatar_component_clause,[],[f151])).
% 3.56/0.88  fof(f1392,plain,(
% 3.56/0.88    spl5_132 | ~spl5_33 | ~spl5_48 | ~spl5_98),
% 3.56/0.88    inference(avatar_split_clause,[],[f873,f869,f424,f280,f1389])).
% 3.56/0.88  fof(f424,plain,(
% 3.56/0.88    spl5_48 <=> v4_relat_1(sK2,k1_tarski(sK0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 3.56/0.89  fof(f873,plain,(
% 3.56/0.89    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | (~spl5_33 | ~spl5_48 | ~spl5_98)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f426,f282,f870])).
% 3.56/0.89  fof(f426,plain,(
% 3.56/0.89    v4_relat_1(sK2,k1_tarski(sK0)) | ~spl5_48),
% 3.56/0.89    inference(avatar_component_clause,[],[f424])).
% 3.56/0.89  fof(f1264,plain,(
% 3.56/0.89    spl5_124 | ~spl5_31 | ~spl5_33),
% 3.56/0.89    inference(avatar_split_clause,[],[f336,f280,f272,f1262])).
% 3.56/0.89  fof(f336,plain,(
% 3.56/0.89    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))) ) | (~spl5_31 | ~spl5_33)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f282,f273])).
% 3.56/0.89  fof(f1244,plain,(
% 3.56/0.89    ~spl5_123 | ~spl5_1 | ~spl5_33 | ~spl5_47 | spl5_63),
% 3.56/0.89    inference(avatar_split_clause,[],[f1223,f543,f420,f280,f122,f1241])).
% 3.56/0.89  fof(f122,plain,(
% 3.56/0.89    spl5_1 <=> v1_funct_1(sK2)),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.56/0.89  fof(f420,plain,(
% 3.56/0.89    spl5_47 <=> ! [X1,X0] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 3.56/0.89  fof(f543,plain,(
% 3.56/0.89    spl5_63 <=> k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 3.56/0.89  fof(f1223,plain,(
% 3.56/0.89    k1_tarski(sK0) != k1_relat_1(sK2) | (~spl5_1 | ~spl5_33 | ~spl5_47 | spl5_63)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f282,f124,f545,f421])).
% 3.56/0.89  fof(f421,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl5_47),
% 3.56/0.89    inference(avatar_component_clause,[],[f420])).
% 3.56/0.89  fof(f545,plain,(
% 3.56/0.89    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | spl5_63),
% 3.56/0.89    inference(avatar_component_clause,[],[f543])).
% 3.56/0.89  fof(f124,plain,(
% 3.56/0.89    v1_funct_1(sK2) | ~spl5_1),
% 3.56/0.89    inference(avatar_component_clause,[],[f122])).
% 3.56/0.89  fof(f1073,plain,(
% 3.56/0.89    spl5_114 | ~spl5_43 | ~spl5_50),
% 3.56/0.89    inference(avatar_split_clause,[],[f443,f438,f386,f1071])).
% 3.56/0.89  fof(f386,plain,(
% 3.56/0.89    spl5_43 <=> ! [X1,X0,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 3.56/0.89  fof(f438,plain,(
% 3.56/0.89    spl5_50 <=> ! [X1,X3,X0,X2] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 3.56/0.89  fof(f443,plain,(
% 3.56/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) ) | (~spl5_43 | ~spl5_50)),
% 3.56/0.89    inference(duplicate_literal_removal,[],[f442])).
% 3.56/0.89  fof(f442,plain,(
% 3.56/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_43 | ~spl5_50)),
% 3.56/0.89    inference(superposition,[],[f439,f387])).
% 3.56/0.89  fof(f387,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_43),
% 3.56/0.89    inference(avatar_component_clause,[],[f386])).
% 3.56/0.89  fof(f439,plain,(
% 3.56/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) ) | ~spl5_50),
% 3.56/0.89    inference(avatar_component_clause,[],[f438])).
% 3.56/0.89  fof(f871,plain,(
% 3.56/0.89    spl5_98 | ~spl5_34 | ~spl5_35),
% 3.56/0.89    inference(avatar_split_clause,[],[f344,f289,f285,f869])).
% 3.56/0.89  fof(f285,plain,(
% 3.56/0.89    spl5_34 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 3.56/0.89  fof(f289,plain,(
% 3.56/0.89    spl5_35 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 3.56/0.89  fof(f344,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | (~spl5_34 | ~spl5_35)),
% 3.56/0.89    inference(duplicate_literal_removal,[],[f343])).
% 3.56/0.89  fof(f343,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | (~spl5_34 | ~spl5_35)),
% 3.56/0.89    inference(superposition,[],[f286,f290])).
% 3.56/0.89  fof(f290,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl5_35),
% 3.56/0.89    inference(avatar_component_clause,[],[f289])).
% 3.56/0.89  fof(f286,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl5_34),
% 3.56/0.89    inference(avatar_component_clause,[],[f285])).
% 3.56/0.89  fof(f656,plain,(
% 3.56/0.89    spl5_76 | ~spl5_19 | ~spl5_23),
% 3.56/0.89    inference(avatar_split_clause,[],[f262,f222,f203,f654])).
% 3.56/0.89  fof(f203,plain,(
% 3.56/0.89    spl5_19 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.56/0.89  fof(f222,plain,(
% 3.56/0.89    spl5_23 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.56/0.89  fof(f262,plain,(
% 3.56/0.89    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) ) | (~spl5_19 | ~spl5_23)),
% 3.56/0.89    inference(resolution,[],[f223,f204])).
% 3.56/0.89  fof(f204,plain,(
% 3.56/0.89    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl5_19),
% 3.56/0.89    inference(avatar_component_clause,[],[f203])).
% 3.56/0.89  fof(f223,plain,(
% 3.56/0.89    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) ) | ~spl5_23),
% 3.56/0.89    inference(avatar_component_clause,[],[f222])).
% 3.56/0.89  fof(f606,plain,(
% 3.56/0.89    spl5_70 | ~spl5_6 | ~spl5_13 | ~spl5_25),
% 3.56/0.89    inference(avatar_split_clause,[],[f296,f236,f177,f147,f603])).
% 3.56/0.89  fof(f147,plain,(
% 3.56/0.89    spl5_6 <=> ! [X0] : v1_relat_1(sK3(X0))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.56/0.89  fof(f177,plain,(
% 3.56/0.89    spl5_13 <=> ! [X0] : k1_relat_1(sK3(X0)) = X0),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.56/0.89  fof(f236,plain,(
% 3.56/0.89    spl5_25 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.56/0.89  fof(f296,plain,(
% 3.56/0.89    k1_xboole_0 = sK3(k1_xboole_0) | (~spl5_6 | ~spl5_13 | ~spl5_25)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f148,f178,f237])).
% 3.56/0.89  fof(f237,plain,(
% 3.56/0.89    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl5_25),
% 3.56/0.89    inference(avatar_component_clause,[],[f236])).
% 3.56/0.89  fof(f178,plain,(
% 3.56/0.89    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) ) | ~spl5_13),
% 3.56/0.89    inference(avatar_component_clause,[],[f177])).
% 3.56/0.89  fof(f148,plain,(
% 3.56/0.89    ( ! [X0] : (v1_relat_1(sK3(X0))) ) | ~spl5_6),
% 3.56/0.89    inference(avatar_component_clause,[],[f147])).
% 3.56/0.89  fof(f578,plain,(
% 3.56/0.89    spl5_68 | ~spl5_17 | ~spl5_18),
% 3.56/0.89    inference(avatar_split_clause,[],[f215,f197,f193,f576])).
% 3.56/0.89  fof(f193,plain,(
% 3.56/0.89    spl5_17 <=> ! [X1,X4] : r2_hidden(X4,k2_tarski(X4,X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.56/0.89  fof(f197,plain,(
% 3.56/0.89    spl5_18 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.56/0.89  fof(f215,plain,(
% 3.56/0.89    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) ) | (~spl5_17 | ~spl5_18)),
% 3.56/0.89    inference(superposition,[],[f194,f198])).
% 3.56/0.89  fof(f198,plain,(
% 3.56/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl5_18),
% 3.56/0.89    inference(avatar_component_clause,[],[f197])).
% 3.56/0.89  fof(f194,plain,(
% 3.56/0.89    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) ) | ~spl5_17),
% 3.56/0.89    inference(avatar_component_clause,[],[f193])).
% 3.56/0.89  fof(f564,plain,(
% 3.56/0.89    spl5_65 | ~spl5_11 | ~spl5_29),
% 3.56/0.89    inference(avatar_split_clause,[],[f303,f253,f169,f562])).
% 3.56/0.89  fof(f253,plain,(
% 3.56/0.89    spl5_29 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 3.56/0.89  fof(f303,plain,(
% 3.56/0.89    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | (~spl5_11 | ~spl5_29)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f170,f254])).
% 3.56/0.89  fof(f254,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl5_29),
% 3.56/0.89    inference(avatar_component_clause,[],[f253])).
% 3.56/0.89  fof(f546,plain,(
% 3.56/0.89    ~spl5_4 | ~spl5_63 | spl5_5 | ~spl5_43),
% 3.56/0.89    inference(avatar_split_clause,[],[f406,f386,f142,f543,f137])).
% 3.56/0.89  fof(f137,plain,(
% 3.56/0.89    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.56/0.89  fof(f142,plain,(
% 3.56/0.89    spl5_5 <=> k2_relset_1(k1_tarski(sK0),sK1,sK2) = k1_tarski(k1_funct_1(sK2,sK0))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.56/0.89  fof(f406,plain,(
% 3.56/0.89    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | (spl5_5 | ~spl5_43)),
% 3.56/0.89    inference(superposition,[],[f144,f387])).
% 3.56/0.89  fof(f144,plain,(
% 3.56/0.89    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) | spl5_5),
% 3.56/0.89    inference(avatar_component_clause,[],[f142])).
% 3.56/0.89  fof(f502,plain,(
% 3.56/0.89    spl5_56 | ~spl5_19 | ~spl5_54),
% 3.56/0.89    inference(avatar_split_clause,[],[f489,f485,f203,f499])).
% 3.56/0.89  fof(f485,plain,(
% 3.56/0.89    spl5_54 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0)))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 3.56/0.89  fof(f489,plain,(
% 3.56/0.89    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) | (~spl5_19 | ~spl5_54)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f487,f204])).
% 3.56/0.89  fof(f487,plain,(
% 3.56/0.89    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0))) | ~spl5_54),
% 3.56/0.89    inference(avatar_component_clause,[],[f485])).
% 3.56/0.89  fof(f488,plain,(
% 3.56/0.89    spl5_54 | ~spl5_4 | ~spl5_42 | ~spl5_44),
% 3.56/0.89    inference(avatar_split_clause,[],[f418,f390,f382,f137,f485])).
% 3.56/0.89  fof(f382,plain,(
% 3.56/0.89    spl5_42 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 3.56/0.89  fof(f390,plain,(
% 3.56/0.89    spl5_44 <=> ! [X1,X0,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 3.56/0.89  fof(f418,plain,(
% 3.56/0.89    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_tarski(sK0))) | (~spl5_4 | ~spl5_42 | ~spl5_44)),
% 3.56/0.89    inference(forward_demodulation,[],[f408,f401])).
% 3.56/0.89  fof(f401,plain,(
% 3.56/0.89    k1_relat_1(sK2) = k1_relset_1(k1_tarski(sK0),sK1,sK2) | (~spl5_4 | ~spl5_42)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f139,f383])).
% 3.56/0.89  fof(f383,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_42),
% 3.56/0.89    inference(avatar_component_clause,[],[f382])).
% 3.56/0.89  fof(f139,plain,(
% 3.56/0.89    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl5_4),
% 3.56/0.89    inference(avatar_component_clause,[],[f137])).
% 3.56/0.89  fof(f408,plain,(
% 3.56/0.89    m1_subset_1(k1_relset_1(k1_tarski(sK0),sK1,sK2),k1_zfmisc_1(k1_tarski(sK0))) | (~spl5_4 | ~spl5_44)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f139,f391])).
% 3.56/0.89  fof(f391,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_44),
% 3.56/0.89    inference(avatar_component_clause,[],[f390])).
% 3.56/0.89  fof(f440,plain,(
% 3.56/0.89    spl5_50),
% 3.56/0.89    inference(avatar_split_clause,[],[f109,f438])).
% 3.56/0.89  fof(f109,plain,(
% 3.56/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f48])).
% 3.56/0.89  fof(f48,plain,(
% 3.56/0.89    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.56/0.89    inference(flattening,[],[f47])).
% 3.56/0.89  fof(f47,plain,(
% 3.56/0.89    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.56/0.89    inference(ennf_transformation,[],[f24])).
% 3.56/0.89  fof(f24,axiom,(
% 3.56/0.89    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 3.56/0.89  fof(f427,plain,(
% 3.56/0.89    spl5_48 | ~spl5_4 | ~spl5_29),
% 3.56/0.89    inference(avatar_split_clause,[],[f302,f253,f137,f424])).
% 3.56/0.89  fof(f302,plain,(
% 3.56/0.89    v4_relat_1(sK2,k1_tarski(sK0)) | (~spl5_4 | ~spl5_29)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f139,f254])).
% 3.56/0.89  fof(f422,plain,(
% 3.56/0.89    spl5_47),
% 3.56/0.89    inference(avatar_split_clause,[],[f86,f420])).
% 3.56/0.89  fof(f86,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f37])).
% 3.56/0.89  fof(f37,plain,(
% 3.56/0.89    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.56/0.89    inference(flattening,[],[f36])).
% 3.56/0.89  fof(f36,plain,(
% 3.56/0.89    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.56/0.89    inference(ennf_transformation,[],[f17])).
% 3.56/0.89  fof(f17,axiom,(
% 3.56/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 3.56/0.89  fof(f392,plain,(
% 3.56/0.89    spl5_44),
% 3.56/0.89    inference(avatar_split_clause,[],[f99,f390])).
% 3.56/0.89  fof(f99,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f43])).
% 3.56/0.89  fof(f43,plain,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    inference(ennf_transformation,[],[f20])).
% 3.56/0.89  fof(f20,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 3.56/0.89  fof(f388,plain,(
% 3.56/0.89    spl5_43),
% 3.56/0.89    inference(avatar_split_clause,[],[f98,f386])).
% 3.56/0.89  fof(f98,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f42])).
% 3.56/0.89  fof(f42,plain,(
% 3.56/0.89    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    inference(ennf_transformation,[],[f22])).
% 3.56/0.89  fof(f22,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.56/0.89  fof(f384,plain,(
% 3.56/0.89    spl5_42),
% 3.56/0.89    inference(avatar_split_clause,[],[f97,f382])).
% 3.56/0.89  fof(f97,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f41])).
% 3.56/0.89  fof(f41,plain,(
% 3.56/0.89    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    inference(ennf_transformation,[],[f21])).
% 3.56/0.89  fof(f21,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.56/0.89  fof(f325,plain,(
% 3.56/0.89    spl5_38),
% 3.56/0.89    inference(avatar_split_clause,[],[f84,f323])).
% 3.56/0.89  fof(f84,plain,(
% 3.56/0.89    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f53])).
% 3.56/0.89  fof(f53,plain,(
% 3.56/0.89    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.56/0.89    inference(nnf_transformation,[],[f34])).
% 3.56/0.89  fof(f34,plain,(
% 3.56/0.89    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.56/0.89    inference(ennf_transformation,[],[f13])).
% 3.56/0.89  fof(f13,axiom,(
% 3.56/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 3.56/0.89  fof(f321,plain,(
% 3.56/0.89    spl5_37),
% 3.56/0.89    inference(avatar_split_clause,[],[f83,f319])).
% 3.56/0.89  fof(f83,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f53])).
% 3.56/0.89  fof(f291,plain,(
% 3.56/0.89    spl5_35),
% 3.56/0.89    inference(avatar_split_clause,[],[f87,f289])).
% 3.56/0.89  fof(f87,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f39])).
% 3.56/0.89  fof(f39,plain,(
% 3.56/0.89    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.56/0.89    inference(flattening,[],[f38])).
% 3.56/0.89  fof(f38,plain,(
% 3.56/0.89    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.56/0.89    inference(ennf_transformation,[],[f14])).
% 3.56/0.89  fof(f14,axiom,(
% 3.56/0.89    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 3.56/0.89  fof(f287,plain,(
% 3.56/0.89    spl5_34),
% 3.56/0.89    inference(avatar_split_clause,[],[f82,f285])).
% 3.56/0.89  fof(f82,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f33])).
% 3.56/0.89  fof(f33,plain,(
% 3.56/0.89    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.56/0.89    inference(ennf_transformation,[],[f12])).
% 3.56/0.89  fof(f12,axiom,(
% 3.56/0.89    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.56/0.89  fof(f283,plain,(
% 3.56/0.89    spl5_33 | ~spl5_4 | ~spl5_24),
% 3.56/0.89    inference(avatar_split_clause,[],[f263,f226,f137,f280])).
% 3.56/0.89  fof(f226,plain,(
% 3.56/0.89    spl5_24 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.56/0.89  fof(f263,plain,(
% 3.56/0.89    v1_relat_1(sK2) | (~spl5_4 | ~spl5_24)),
% 3.56/0.89    inference(unit_resulting_resolution,[],[f139,f227])).
% 3.56/0.89  fof(f227,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl5_24),
% 3.56/0.89    inference(avatar_component_clause,[],[f226])).
% 3.56/0.89  fof(f274,plain,(
% 3.56/0.89    spl5_31),
% 3.56/0.89    inference(avatar_split_clause,[],[f75,f272])).
% 3.56/0.89  fof(f75,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f31])).
% 3.56/0.89  fof(f31,plain,(
% 3.56/0.89    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.56/0.89    inference(ennf_transformation,[],[f10])).
% 3.56/0.89  fof(f10,axiom,(
% 3.56/0.89    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 3.56/0.89  fof(f255,plain,(
% 3.56/0.89    spl5_29),
% 3.56/0.89    inference(avatar_split_clause,[],[f100,f253])).
% 3.56/0.89  fof(f100,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f44])).
% 3.56/0.89  fof(f44,plain,(
% 3.56/0.89    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    inference(ennf_transformation,[],[f19])).
% 3.56/0.89  fof(f19,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.56/0.89  fof(f251,plain,(
% 3.56/0.89    spl5_28),
% 3.56/0.89    inference(avatar_split_clause,[],[f90,f249])).
% 3.56/0.89  fof(f90,plain,(
% 3.56/0.89    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f55])).
% 3.56/0.89  fof(f55,plain,(
% 3.56/0.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/0.89    inference(flattening,[],[f54])).
% 3.56/0.89  fof(f54,plain,(
% 3.56/0.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/0.89    inference(nnf_transformation,[],[f1])).
% 3.56/0.89  fof(f1,axiom,(
% 3.56/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.56/0.89  fof(f242,plain,(
% 3.56/0.89    spl5_26),
% 3.56/0.89    inference(avatar_split_clause,[],[f74,f240])).
% 3.56/0.89  fof(f74,plain,(
% 3.56/0.89    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f30])).
% 3.56/0.89  fof(f30,plain,(
% 3.56/0.89    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.56/0.89    inference(flattening,[],[f29])).
% 3.56/0.89  fof(f29,plain,(
% 3.56/0.89    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.56/0.89    inference(ennf_transformation,[],[f16])).
% 3.56/0.89  fof(f16,axiom,(
% 3.56/0.89    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 3.56/0.89  fof(f238,plain,(
% 3.56/0.89    spl5_25),
% 3.56/0.89    inference(avatar_split_clause,[],[f73,f236])).
% 3.56/0.89  fof(f73,plain,(
% 3.56/0.89    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f30])).
% 3.56/0.89  fof(f228,plain,(
% 3.56/0.89    spl5_24),
% 3.56/0.89    inference(avatar_split_clause,[],[f96,f226])).
% 3.56/0.89  fof(f96,plain,(
% 3.56/0.89    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f40])).
% 3.56/0.89  fof(f40,plain,(
% 3.56/0.89    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/0.89    inference(ennf_transformation,[],[f18])).
% 3.56/0.89  fof(f18,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.56/0.89  fof(f224,plain,(
% 3.56/0.89    spl5_23),
% 3.56/0.89    inference(avatar_split_clause,[],[f85,f222])).
% 3.56/0.89  fof(f85,plain,(
% 3.56/0.89    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f35])).
% 3.56/0.89  fof(f35,plain,(
% 3.56/0.89    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.56/0.89    inference(ennf_transformation,[],[f7])).
% 3.56/0.89  fof(f7,axiom,(
% 3.56/0.89    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 3.56/0.89  fof(f214,plain,(
% 3.56/0.89    spl5_21 | ~spl5_12 | ~spl5_14),
% 3.56/0.89    inference(avatar_split_clause,[],[f200,f181,f173,f211])).
% 3.56/0.89  fof(f173,plain,(
% 3.56/0.89    spl5_12 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.56/0.89  fof(f181,plain,(
% 3.56/0.89    spl5_14 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 3.56/0.89    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.56/0.89  fof(f200,plain,(
% 3.56/0.89    v1_relat_1(k1_xboole_0) | (~spl5_12 | ~spl5_14)),
% 3.56/0.89    inference(superposition,[],[f174,f182])).
% 3.56/0.89  fof(f182,plain,(
% 3.56/0.89    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_14),
% 3.56/0.89    inference(avatar_component_clause,[],[f181])).
% 3.56/0.89  fof(f174,plain,(
% 3.56/0.89    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_12),
% 3.56/0.89    inference(avatar_component_clause,[],[f173])).
% 3.56/0.89  fof(f205,plain,(
% 3.56/0.89    spl5_19),
% 3.56/0.89    inference(avatar_split_clause,[],[f91,f203])).
% 3.56/0.89  fof(f91,plain,(
% 3.56/0.89    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f56])).
% 3.56/0.89  fof(f56,plain,(
% 3.56/0.89    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.56/0.89    inference(nnf_transformation,[],[f8])).
% 3.56/0.89  fof(f8,axiom,(
% 3.56/0.89    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.56/0.89  fof(f199,plain,(
% 3.56/0.89    spl5_18),
% 3.56/0.89    inference(avatar_split_clause,[],[f72,f197])).
% 3.56/0.89  fof(f72,plain,(
% 3.56/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.56/0.89    inference(cnf_transformation,[],[f3])).
% 3.56/0.89  fof(f3,axiom,(
% 3.56/0.89    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.56/0.89  fof(f195,plain,(
% 3.56/0.89    spl5_17),
% 3.56/0.89    inference(avatar_split_clause,[],[f117,f193])).
% 3.56/0.89  fof(f117,plain,(
% 3.56/0.89    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.56/0.89    inference(equality_resolution,[],[f116])).
% 3.56/0.89  fof(f116,plain,(
% 3.56/0.89    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.56/0.89    inference(equality_resolution,[],[f104])).
% 3.56/0.89  fof(f104,plain,(
% 3.56/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.56/0.89    inference(cnf_transformation,[],[f63])).
% 3.56/0.89  fof(f63,plain,(
% 3.56/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.56/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f61,f62])).
% 3.56/0.89  fof(f62,plain,(
% 3.56/0.89    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.56/0.89    introduced(choice_axiom,[])).
% 3.56/0.89  fof(f61,plain,(
% 3.56/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.56/0.89    inference(rectify,[],[f60])).
% 3.56/0.89  fof(f60,plain,(
% 3.56/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.56/0.89    inference(flattening,[],[f59])).
% 3.56/0.89  fof(f59,plain,(
% 3.56/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.56/0.89    inference(nnf_transformation,[],[f2])).
% 3.56/0.89  fof(f2,axiom,(
% 3.56/0.89    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.56/0.89  fof(f183,plain,(
% 3.56/0.89    spl5_14),
% 3.56/0.89    inference(avatar_split_clause,[],[f112,f181])).
% 3.56/0.89  fof(f112,plain,(
% 3.56/0.89    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.56/0.89    inference(equality_resolution,[],[f95])).
% 3.56/0.89  fof(f95,plain,(
% 3.56/0.89    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.56/0.89    inference(cnf_transformation,[],[f58])).
% 3.56/0.89  fof(f58,plain,(
% 3.56/0.89    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.56/0.89    inference(flattening,[],[f57])).
% 3.56/0.89  fof(f57,plain,(
% 3.56/0.89    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.56/0.89    inference(nnf_transformation,[],[f5])).
% 3.56/0.89  fof(f5,axiom,(
% 3.56/0.89    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.56/0.89  fof(f179,plain,(
% 3.56/0.89    spl5_13),
% 3.56/0.89    inference(avatar_split_clause,[],[f78,f177])).
% 3.56/0.89  fof(f78,plain,(
% 3.56/0.89    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 3.56/0.89    inference(cnf_transformation,[],[f52])).
% 3.56/0.89  fof(f52,plain,(
% 3.56/0.89    ! [X0] : (! [X2] : (k1_tarski(X2) = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 3.56/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f51])).
% 3.56/0.89  fof(f51,plain,(
% 3.56/0.89    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_tarski(X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_tarski(X2) = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 3.56/0.89    introduced(choice_axiom,[])).
% 3.56/0.89  fof(f32,plain,(
% 3.56/0.89    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_tarski(X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.56/0.89    inference(ennf_transformation,[],[f23])).
% 3.56/0.89  fof(f23,axiom,(
% 3.56/0.89    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_tarski(X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).
% 3.56/0.89  fof(f175,plain,(
% 3.56/0.89    spl5_12),
% 3.56/0.89    inference(avatar_split_clause,[],[f80,f173])).
% 3.56/0.89  fof(f80,plain,(
% 3.56/0.89    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f11])).
% 3.56/0.89  fof(f11,axiom,(
% 3.56/0.89    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.56/0.89  fof(f171,plain,(
% 3.56/0.89    spl5_11),
% 3.56/0.89    inference(avatar_split_clause,[],[f71,f169])).
% 3.56/0.89  fof(f71,plain,(
% 3.56/0.89    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f6])).
% 3.56/0.89  fof(f6,axiom,(
% 3.56/0.89    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.56/0.89  fof(f167,plain,(
% 3.56/0.89    spl5_10),
% 3.56/0.89    inference(avatar_split_clause,[],[f70,f164])).
% 3.56/0.89  fof(f70,plain,(
% 3.56/0.89    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.56/0.89    inference(cnf_transformation,[],[f15])).
% 3.56/0.89  fof(f15,axiom,(
% 3.56/0.89    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 3.56/0.89  fof(f162,plain,(
% 3.56/0.89    spl5_9),
% 3.56/0.89    inference(avatar_split_clause,[],[f69,f159])).
% 3.56/0.89  fof(f69,plain,(
% 3.56/0.89    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/0.89    inference(cnf_transformation,[],[f15])).
% 3.56/0.89  fof(f153,plain,(
% 3.56/0.89    spl5_7),
% 3.56/0.89    inference(avatar_split_clause,[],[f77,f151])).
% 3.56/0.89  fof(f77,plain,(
% 3.56/0.89    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f52])).
% 3.56/0.89  fof(f149,plain,(
% 3.56/0.89    spl5_6),
% 3.56/0.89    inference(avatar_split_clause,[],[f76,f147])).
% 3.56/0.89  fof(f76,plain,(
% 3.56/0.89    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 3.56/0.89    inference(cnf_transformation,[],[f52])).
% 3.56/0.89  fof(f145,plain,(
% 3.56/0.89    ~spl5_5),
% 3.56/0.89    inference(avatar_split_clause,[],[f68,f142])).
% 3.56/0.89  fof(f68,plain,(
% 3.56/0.89    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 3.56/0.89    inference(cnf_transformation,[],[f50])).
% 3.56/0.89  fof(f50,plain,(
% 3.56/0.89    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 3.56/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f49])).
% 3.56/0.89  fof(f49,plain,(
% 3.56/0.89    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 3.56/0.89    introduced(choice_axiom,[])).
% 3.56/0.89  fof(f28,plain,(
% 3.56/0.89    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.56/0.89    inference(flattening,[],[f27])).
% 3.56/0.89  fof(f27,plain,(
% 3.56/0.89    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.56/0.89    inference(ennf_transformation,[],[f26])).
% 3.56/0.89  fof(f26,negated_conjecture,(
% 3.56/0.89    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 3.56/0.89    inference(negated_conjecture,[],[f25])).
% 3.56/0.89  fof(f25,conjecture,(
% 3.56/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 3.56/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 3.56/0.89  fof(f140,plain,(
% 3.56/0.89    spl5_4),
% 3.56/0.89    inference(avatar_split_clause,[],[f66,f137])).
% 3.56/0.89  fof(f66,plain,(
% 3.56/0.89    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.56/0.89    inference(cnf_transformation,[],[f50])).
% 3.56/0.89  fof(f135,plain,(
% 3.56/0.89    spl5_3),
% 3.56/0.89    inference(avatar_split_clause,[],[f65,f132])).
% 3.56/0.89  fof(f65,plain,(
% 3.56/0.89    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 3.56/0.89    inference(cnf_transformation,[],[f50])).
% 3.56/0.89  fof(f130,plain,(
% 3.56/0.89    ~spl5_2),
% 3.56/0.89    inference(avatar_split_clause,[],[f67,f127])).
% 3.56/0.89  fof(f67,plain,(
% 3.56/0.89    k1_xboole_0 != sK1),
% 3.56/0.89    inference(cnf_transformation,[],[f50])).
% 3.56/0.89  fof(f125,plain,(
% 3.56/0.89    spl5_1),
% 3.56/0.89    inference(avatar_split_clause,[],[f64,f122])).
% 3.56/0.89  fof(f64,plain,(
% 3.56/0.89    v1_funct_1(sK2)),
% 3.56/0.89    inference(cnf_transformation,[],[f50])).
% 3.56/0.89  % SZS output end Proof for theBenchmark
% 3.56/0.89  % (19346)------------------------------
% 3.56/0.89  % (19346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.89  % (19346)Termination reason: Refutation
% 3.56/0.89  
% 3.56/0.89  % (19346)Memory used [KB]: 8443
% 3.56/0.89  % (19346)Time elapsed: 0.266 s
% 3.56/0.89  % (19346)------------------------------
% 3.56/0.89  % (19346)------------------------------
% 3.56/0.89  % (19303)Success in time 0.519 s
%------------------------------------------------------------------------------
