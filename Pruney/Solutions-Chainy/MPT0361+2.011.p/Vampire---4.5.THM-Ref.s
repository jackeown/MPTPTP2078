%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 350 expanded)
%              Number of leaves         :   57 ( 172 expanded)
%              Depth                    :    7
%              Number of atoms          :  547 ( 895 expanded)
%              Number of equality atoms :   77 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3587,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f74,f78,f82,f86,f90,f94,f106,f110,f114,f118,f122,f131,f156,f167,f188,f192,f200,f230,f234,f269,f278,f289,f331,f353,f386,f492,f577,f581,f697,f1054,f1551,f1716,f1822,f2357,f2391,f2822,f3240,f3405,f3585])).

fof(f3585,plain,
    ( ~ spl4_4
    | ~ spl4_27
    | ~ spl4_102
    | ~ spl4_129
    | spl4_141
    | ~ spl4_143 ),
    inference(avatar_contradiction_clause,[],[f3584])).

fof(f3584,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_27
    | ~ spl4_102
    | ~ spl4_129
    | spl4_141
    | ~ spl4_143 ),
    inference(subsumption_resolution,[],[f3583,f73])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3583,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_27
    | ~ spl4_102
    | ~ spl4_129
    | spl4_141
    | ~ spl4_143 ),
    inference(forward_demodulation,[],[f3582,f2862])).

fof(f2862,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))
    | ~ spl4_102
    | ~ spl4_129 ),
    inference(superposition,[],[f2821,f1550])).

fof(f1550,plain,
    ( ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f1549,plain,
    ( spl4_102
  <=> ! [X3,X4] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f2821,plain,
    ( ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))
    | ~ spl4_129 ),
    inference(avatar_component_clause,[],[f2820])).

fof(f2820,plain,
    ( spl4_129
  <=> ! [X9,X7,X8] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f3582,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl4_27
    | spl4_141
    | ~ spl4_143 ),
    inference(forward_demodulation,[],[f3579,f199])).

fof(f199,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f3579,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK1),sK0)
    | spl4_141
    | ~ spl4_143 ),
    inference(resolution,[],[f3404,f3239])).

fof(f3239,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0)
    | spl4_141 ),
    inference(avatar_component_clause,[],[f3238])).

fof(f3238,plain,
    ( spl4_141
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f3404,plain,
    ( ! [X1] :
        ( r1_tarski(X1,sK0)
        | ~ r1_tarski(k4_xboole_0(X1,sK1),sK0) )
    | ~ spl4_143 ),
    inference(avatar_component_clause,[],[f3403])).

fof(f3403,plain,
    ( spl4_143
  <=> ! [X1] :
        ( r1_tarski(X1,sK0)
        | ~ r1_tarski(k4_xboole_0(X1,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f3405,plain,
    ( spl4_143
    | ~ spl4_22
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1908,f1820,f165,f3403])).

fof(f165,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
        | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1820,plain,
    ( spl4_108
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1908,plain,
    ( ! [X1] :
        ( r1_tarski(X1,sK0)
        | ~ r1_tarski(k4_xboole_0(X1,sK1),sK0) )
    | ~ spl4_22
    | ~ spl4_108 ),
    inference(superposition,[],[f166,f1821])).

fof(f1821,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f3240,plain,
    ( ~ spl4_141
    | ~ spl4_83
    | spl4_123 ),
    inference(avatar_split_clause,[],[f2473,f2389,f1052,f3238])).

fof(f1052,plain,
    ( spl4_83
  <=> ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_tarski(k4_xboole_0(X0,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f2389,plain,
    ( spl4_123
  <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f2473,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0)
    | ~ spl4_83
    | spl4_123 ),
    inference(resolution,[],[f2390,f1053])).

fof(f1053,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_tarski(k4_xboole_0(X0,sK2),sK0) )
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f2390,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_123 ),
    inference(avatar_component_clause,[],[f2389])).

fof(f2822,plain,
    ( spl4_129
    | ~ spl4_8
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f715,f695,f88,f2820])).

fof(f88,plain,
    ( spl4_8
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f695,plain,
    ( spl4_64
  <=> ! [X3,X5,X4,X6] : k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f715,plain,
    ( ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))
    | ~ spl4_8
    | ~ spl4_64 ),
    inference(superposition,[],[f696,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f696,plain,
    ( ! [X6,X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f695])).

fof(f2391,plain,
    ( ~ spl4_123
    | spl4_37
    | ~ spl4_47
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f2383,f2355,f384,f287,f2389])).

fof(f287,plain,
    ( spl4_37
  <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f384,plain,
    ( spl4_47
  <=> ! [X3,X5,X4] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f2355,plain,
    ( spl4_120
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f2383,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_37
    | ~ spl4_47
    | ~ spl4_120 ),
    inference(subsumption_resolution,[],[f2370,f385])).

fof(f385,plain,
    ( ! [X4,X5,X3] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f384])).

fof(f2370,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_37
    | ~ spl4_120 ),
    inference(superposition,[],[f288,f2356])).

fof(f2356,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f2355])).

fof(f288,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f287])).

fof(f2357,plain,
    ( spl4_120
    | ~ spl4_13
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f582,f579,f108,f2355])).

fof(f108,plain,
    ( spl4_13
  <=> ! [X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f579,plain,
    ( spl4_59
  <=> ! [X3,X2] :
        ( k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)
        | ~ r2_hidden(X3,k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f582,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_13
    | ~ spl4_59 ),
    inference(resolution,[],[f580,f109])).

fof(f109,plain,
    ( ! [X2,X0] :
        ( r2_hidden(X2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X2,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f580,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k1_zfmisc_1(X2))
        | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f579])).

fof(f1822,plain,
    ( spl4_108
    | ~ spl4_2
    | ~ spl4_105 ),
    inference(avatar_split_clause,[],[f1722,f1714,f64,f1820])).

fof(f64,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1714,plain,
    ( spl4_105
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f1722,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_105 ),
    inference(resolution,[],[f1715,f65])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f1715,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_105 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1716,plain,
    ( spl4_105
    | ~ spl4_16
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f354,f351,f120,f1714])).

fof(f120,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f351,plain,
    ( spl4_44
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_16
    | ~ spl4_44 ),
    inference(resolution,[],[f352,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f351])).

fof(f1551,plain,
    ( spl4_102
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f147,f129,f120,f1549])).

fof(f129,plain,
    ( spl4_17
  <=> ! [X3,X2] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f147,plain,
    ( ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(resolution,[],[f121,f130])).

fof(f130,plain,
    ( ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1054,plain,
    ( spl4_83
    | ~ spl4_22
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f592,f575,f165,f1052])).

fof(f575,plain,
    ( spl4_58
  <=> sK0 = k2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f592,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_tarski(k4_xboole_0(X0,sK2),sK0) )
    | ~ spl4_22
    | ~ spl4_58 ),
    inference(superposition,[],[f166,f576])).

fof(f576,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f575])).

fof(f697,plain,
    ( spl4_64
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f253,f198,f695])).

fof(f253,plain,
    ( ! [X6,X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f252,f199])).

fof(f252,plain,
    ( ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6))
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f246,f199])).

fof(f246,plain,
    ( ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X6)
    | ~ spl4_27 ),
    inference(superposition,[],[f199,f199])).

fof(f581,plain,
    ( spl4_59
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f226,f186,f112,f68,f579])).

fof(f68,plain,
    ( spl4_3
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f186,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f226,plain,
    ( ! [X2,X3] :
        ( k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)
        | ~ r2_hidden(X3,k1_zfmisc_1(X2)) )
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f219,f69])).

fof(f69,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f219,plain,
    ( ! [X2,X3] :
        ( k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)
        | ~ r2_hidden(X3,k1_zfmisc_1(X2))
        | v1_xboole_0(k1_zfmisc_1(X2)) )
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(resolution,[],[f187,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f577,plain,
    ( spl4_58
    | ~ spl4_42
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f508,f490,f329,f575])).

fof(f329,plain,
    ( spl4_42
  <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f490,plain,
    ( spl4_53
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f508,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_42
    | ~ spl4_53 ),
    inference(superposition,[],[f330,f491])).

fof(f491,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f490])).

fof(f330,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f329])).

fof(f492,plain,
    ( spl4_53
    | ~ spl4_1
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_29
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f274,f267,f228,f190,f186,f60,f490])).

fof(f60,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f190,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f228,plain,
    ( spl4_29
  <=> k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f267,plain,
    ( spl4_34
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f274,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_29
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f273,f240])).

fof(f240,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f238,f61])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f238,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(superposition,[],[f191,f229])).

fof(f229,plain,
    ( k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f273,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_24
    | ~ spl4_34 ),
    inference(resolution,[],[f268,f187])).

fof(f268,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f267])).

fof(f386,plain,
    ( spl4_47
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f249,f198,f84,f384])).

fof(f84,plain,
    ( spl4_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f249,plain,
    ( ! [X4,X5,X3] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(superposition,[],[f85,f199])).

fof(f85,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f353,plain,
    ( spl4_44
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f144,f116,f104,f68,f351])).

fof(f104,plain,
    ( spl4_12
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f116,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f143,f69])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(resolution,[],[f117,f105])).

fof(f105,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f331,plain,
    ( spl4_42
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f148,f120,f84,f329])).

fof(f148,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f121,f85])).

fof(f289,plain,
    ( ~ spl4_37
    | ~ spl4_1
    | ~ spl4_2
    | spl4_30
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f285,f276,f232,f64,f60,f287])).

fof(f232,plain,
    ( spl4_30
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f276,plain,
    ( spl4_35
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f285,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_30
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f284,f65])).

fof(f284,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1
    | spl4_30
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f283,f61])).

fof(f283,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_30
    | ~ spl4_35 ),
    inference(superposition,[],[f233,f277])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f276])).

fof(f233,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f232])).

fof(f278,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f56,f276])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f269,plain,
    ( spl4_34
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f237,f228,f154,f60,f267])).

fof(f154,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f237,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f236,f61])).

fof(f236,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(superposition,[],[f155,f229])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f234,plain,
    ( ~ spl4_30
    | ~ spl4_2
    | spl4_5
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f225,f186,f76,f64,f232])).

fof(f76,plain,
    ( spl4_5
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f225,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ spl4_2
    | spl4_5
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f77,f217])).

fof(f217,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(resolution,[],[f187,f65])).

fof(f77,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f230,plain,
    ( spl4_29
    | ~ spl4_1
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f216,f186,f60,f228])).

fof(f216,plain,
    ( k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_24 ),
    inference(resolution,[],[f187,f61])).

fof(f200,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f53,f198])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f192,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f48,f190])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f188,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f47,f186])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f167,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f54,f165])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f156,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f46,f154])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f131,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f125,f92,f80,f129])).

fof(f80,plain,
    ( spl4_6
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f92,plain,
    ( spl4_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f125,plain,
    ( ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2))
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(superposition,[],[f81,f93])).

fof(f93,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f81,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f122,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f118,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f44,f116])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f114,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f43,f112])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f58,f108])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f106,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f86,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f82,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f78,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f74,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f66,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:19:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (9220)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (9219)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (9218)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (9228)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (9227)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (9226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (9229)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (9223)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (9222)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (9214)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (9217)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (9216)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (9221)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.54  % (9213)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9212)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (9225)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.55  % (9231)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (9232)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.55  % (9215)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (9224)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9230)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 2.66/0.74  % (9221)Refutation found. Thanks to Tanya!
% 2.66/0.74  % SZS status Theorem for theBenchmark
% 2.66/0.74  % SZS output start Proof for theBenchmark
% 2.66/0.74  fof(f3587,plain,(
% 2.66/0.74    $false),
% 2.66/0.74    inference(avatar_sat_refutation,[],[f62,f66,f70,f74,f78,f82,f86,f90,f94,f106,f110,f114,f118,f122,f131,f156,f167,f188,f192,f200,f230,f234,f269,f278,f289,f331,f353,f386,f492,f577,f581,f697,f1054,f1551,f1716,f1822,f2357,f2391,f2822,f3240,f3405,f3585])).
% 2.66/0.74  fof(f3585,plain,(
% 2.66/0.74    ~spl4_4 | ~spl4_27 | ~spl4_102 | ~spl4_129 | spl4_141 | ~spl4_143),
% 2.66/0.74    inference(avatar_contradiction_clause,[],[f3584])).
% 2.66/0.74  fof(f3584,plain,(
% 2.66/0.74    $false | (~spl4_4 | ~spl4_27 | ~spl4_102 | ~spl4_129 | spl4_141 | ~spl4_143)),
% 2.66/0.74    inference(subsumption_resolution,[],[f3583,f73])).
% 2.66/0.74  fof(f73,plain,(
% 2.66/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_4),
% 2.66/0.74    inference(avatar_component_clause,[],[f72])).
% 2.66/0.74  fof(f72,plain,(
% 2.66/0.74    spl4_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.66/0.74  fof(f3583,plain,(
% 2.66/0.74    ~r1_tarski(k1_xboole_0,sK0) | (~spl4_27 | ~spl4_102 | ~spl4_129 | spl4_141 | ~spl4_143)),
% 2.66/0.74    inference(forward_demodulation,[],[f3582,f2862])).
% 2.66/0.74  fof(f2862,plain,(
% 2.66/0.74    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) ) | (~spl4_102 | ~spl4_129)),
% 2.66/0.74    inference(superposition,[],[f2821,f1550])).
% 2.66/0.74  fof(f1550,plain,(
% 2.66/0.74    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))) ) | ~spl4_102),
% 2.66/0.74    inference(avatar_component_clause,[],[f1549])).
% 2.66/0.74  fof(f1549,plain,(
% 2.66/0.74    spl4_102 <=> ! [X3,X4] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 2.66/0.74  fof(f2821,plain,(
% 2.66/0.74    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))) ) | ~spl4_129),
% 2.66/0.74    inference(avatar_component_clause,[],[f2820])).
% 2.66/0.74  fof(f2820,plain,(
% 2.66/0.74    spl4_129 <=> ! [X9,X7,X8] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).
% 2.66/0.74  fof(f3582,plain,(
% 2.66/0.74    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK1)),sK0) | (~spl4_27 | spl4_141 | ~spl4_143)),
% 2.66/0.74    inference(forward_demodulation,[],[f3579,f199])).
% 2.66/0.74  fof(f199,plain,(
% 2.66/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_27),
% 2.66/0.74    inference(avatar_component_clause,[],[f198])).
% 2.66/0.74  fof(f198,plain,(
% 2.66/0.74    spl4_27 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.66/0.74  fof(f3579,plain,(
% 2.66/0.74    ~r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK1),sK0) | (spl4_141 | ~spl4_143)),
% 2.66/0.74    inference(resolution,[],[f3404,f3239])).
% 2.66/0.74  fof(f3239,plain,(
% 2.66/0.74    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0) | spl4_141),
% 2.66/0.74    inference(avatar_component_clause,[],[f3238])).
% 2.66/0.74  fof(f3238,plain,(
% 2.66/0.74    spl4_141 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 2.66/0.74  fof(f3404,plain,(
% 2.66/0.74    ( ! [X1] : (r1_tarski(X1,sK0) | ~r1_tarski(k4_xboole_0(X1,sK1),sK0)) ) | ~spl4_143),
% 2.66/0.74    inference(avatar_component_clause,[],[f3403])).
% 2.66/0.74  fof(f3403,plain,(
% 2.66/0.74    spl4_143 <=> ! [X1] : (r1_tarski(X1,sK0) | ~r1_tarski(k4_xboole_0(X1,sK1),sK0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 2.66/0.74  fof(f3405,plain,(
% 2.66/0.74    spl4_143 | ~spl4_22 | ~spl4_108),
% 2.66/0.74    inference(avatar_split_clause,[],[f1908,f1820,f165,f3403])).
% 2.66/0.74  fof(f165,plain,(
% 2.66/0.74    spl4_22 <=> ! [X1,X0,X2] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.66/0.74  fof(f1820,plain,(
% 2.66/0.74    spl4_108 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 2.66/0.74  fof(f1908,plain,(
% 2.66/0.74    ( ! [X1] : (r1_tarski(X1,sK0) | ~r1_tarski(k4_xboole_0(X1,sK1),sK0)) ) | (~spl4_22 | ~spl4_108)),
% 2.66/0.74    inference(superposition,[],[f166,f1821])).
% 2.66/0.74  fof(f1821,plain,(
% 2.66/0.74    sK0 = k2_xboole_0(sK1,sK0) | ~spl4_108),
% 2.66/0.74    inference(avatar_component_clause,[],[f1820])).
% 2.66/0.74  fof(f166,plain,(
% 2.66/0.74    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl4_22),
% 2.66/0.74    inference(avatar_component_clause,[],[f165])).
% 2.66/0.74  fof(f3240,plain,(
% 2.66/0.74    ~spl4_141 | ~spl4_83 | spl4_123),
% 2.66/0.74    inference(avatar_split_clause,[],[f2473,f2389,f1052,f3238])).
% 2.66/0.74  fof(f1052,plain,(
% 2.66/0.74    spl4_83 <=> ! [X0] : (r1_tarski(X0,sK0) | ~r1_tarski(k4_xboole_0(X0,sK2),sK0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 2.66/0.74  fof(f2389,plain,(
% 2.66/0.74    spl4_123 <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).
% 2.66/0.74  fof(f2473,plain,(
% 2.66/0.74    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK2),sK0) | (~spl4_83 | spl4_123)),
% 2.66/0.74    inference(resolution,[],[f2390,f1053])).
% 2.66/0.74  fof(f1053,plain,(
% 2.66/0.74    ( ! [X0] : (r1_tarski(X0,sK0) | ~r1_tarski(k4_xboole_0(X0,sK2),sK0)) ) | ~spl4_83),
% 2.66/0.74    inference(avatar_component_clause,[],[f1052])).
% 2.66/0.74  fof(f2390,plain,(
% 2.66/0.74    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_123),
% 2.66/0.74    inference(avatar_component_clause,[],[f2389])).
% 2.66/0.74  fof(f2822,plain,(
% 2.66/0.74    spl4_129 | ~spl4_8 | ~spl4_64),
% 2.66/0.74    inference(avatar_split_clause,[],[f715,f695,f88,f2820])).
% 2.66/0.74  fof(f88,plain,(
% 2.66/0.74    spl4_8 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.66/0.74  fof(f695,plain,(
% 2.66/0.74    spl4_64 <=> ! [X3,X5,X4,X6] : k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 2.66/0.74  fof(f715,plain,(
% 2.66/0.74    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))) ) | (~spl4_8 | ~spl4_64)),
% 2.66/0.74    inference(superposition,[],[f696,f89])).
% 2.66/0.74  fof(f89,plain,(
% 2.66/0.74    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl4_8),
% 2.66/0.74    inference(avatar_component_clause,[],[f88])).
% 2.66/0.74  fof(f696,plain,(
% 2.66/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))) ) | ~spl4_64),
% 2.66/0.74    inference(avatar_component_clause,[],[f695])).
% 2.66/0.74  fof(f2391,plain,(
% 2.66/0.74    ~spl4_123 | spl4_37 | ~spl4_47 | ~spl4_120),
% 2.66/0.74    inference(avatar_split_clause,[],[f2383,f2355,f384,f287,f2389])).
% 2.66/0.74  fof(f287,plain,(
% 2.66/0.74    spl4_37 <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.66/0.74  fof(f384,plain,(
% 2.66/0.74    spl4_47 <=> ! [X3,X5,X4] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.66/0.74  fof(f2355,plain,(
% 2.66/0.74    spl4_120 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).
% 2.66/0.74  fof(f2383,plain,(
% 2.66/0.74    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | (spl4_37 | ~spl4_47 | ~spl4_120)),
% 2.66/0.74    inference(subsumption_resolution,[],[f2370,f385])).
% 2.66/0.74  fof(f385,plain,(
% 2.66/0.74    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))) ) | ~spl4_47),
% 2.66/0.74    inference(avatar_component_clause,[],[f384])).
% 2.66/0.74  fof(f2370,plain,(
% 2.66/0.74    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | (spl4_37 | ~spl4_120)),
% 2.66/0.74    inference(superposition,[],[f288,f2356])).
% 2.66/0.74  fof(f2356,plain,(
% 2.66/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl4_120),
% 2.66/0.74    inference(avatar_component_clause,[],[f2355])).
% 2.66/0.74  fof(f288,plain,(
% 2.66/0.74    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_37),
% 2.66/0.74    inference(avatar_component_clause,[],[f287])).
% 2.66/0.74  fof(f2357,plain,(
% 2.66/0.74    spl4_120 | ~spl4_13 | ~spl4_59),
% 2.66/0.74    inference(avatar_split_clause,[],[f582,f579,f108,f2355])).
% 2.66/0.74  fof(f108,plain,(
% 2.66/0.74    spl4_13 <=> ! [X0,X2] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.66/0.74  fof(f579,plain,(
% 2.66/0.74    spl4_59 <=> ! [X3,X2] : (k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X2)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.66/0.74  fof(f582,plain,(
% 2.66/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) ) | (~spl4_13 | ~spl4_59)),
% 2.66/0.74    inference(resolution,[],[f580,f109])).
% 2.66/0.74  fof(f109,plain,(
% 2.66/0.74    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) ) | ~spl4_13),
% 2.66/0.74    inference(avatar_component_clause,[],[f108])).
% 2.66/0.74  fof(f580,plain,(
% 2.66/0.74    ( ! [X2,X3] : (~r2_hidden(X3,k1_zfmisc_1(X2)) | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)) ) | ~spl4_59),
% 2.66/0.74    inference(avatar_component_clause,[],[f579])).
% 2.66/0.74  fof(f1822,plain,(
% 2.66/0.74    spl4_108 | ~spl4_2 | ~spl4_105),
% 2.66/0.74    inference(avatar_split_clause,[],[f1722,f1714,f64,f1820])).
% 2.66/0.74  fof(f64,plain,(
% 2.66/0.74    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.66/0.74  fof(f1714,plain,(
% 2.66/0.74    spl4_105 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 2.66/0.74  fof(f1722,plain,(
% 2.66/0.74    sK0 = k2_xboole_0(sK1,sK0) | (~spl4_2 | ~spl4_105)),
% 2.66/0.74    inference(resolution,[],[f1715,f65])).
% 2.66/0.74  fof(f65,plain,(
% 2.66/0.74    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 2.66/0.74    inference(avatar_component_clause,[],[f64])).
% 2.66/0.74  fof(f1715,plain,(
% 2.66/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_105),
% 2.66/0.74    inference(avatar_component_clause,[],[f1714])).
% 2.66/0.74  fof(f1716,plain,(
% 2.66/0.74    spl4_105 | ~spl4_16 | ~spl4_44),
% 2.66/0.74    inference(avatar_split_clause,[],[f354,f351,f120,f1714])).
% 2.66/0.74  fof(f120,plain,(
% 2.66/0.74    spl4_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.66/0.74  fof(f351,plain,(
% 2.66/0.74    spl4_44 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.66/0.74  fof(f354,plain,(
% 2.66/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1) ) | (~spl4_16 | ~spl4_44)),
% 2.66/0.74    inference(resolution,[],[f352,f121])).
% 2.66/0.74  fof(f121,plain,(
% 2.66/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_16),
% 2.66/0.74    inference(avatar_component_clause,[],[f120])).
% 2.66/0.74  fof(f352,plain,(
% 2.66/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_44),
% 2.66/0.74    inference(avatar_component_clause,[],[f351])).
% 2.66/0.74  fof(f1551,plain,(
% 2.66/0.74    spl4_102 | ~spl4_16 | ~spl4_17),
% 2.66/0.74    inference(avatar_split_clause,[],[f147,f129,f120,f1549])).
% 2.66/0.74  fof(f129,plain,(
% 2.66/0.74    spl4_17 <=> ! [X3,X2] : r1_tarski(X2,k2_xboole_0(X3,X2))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.66/0.74  fof(f147,plain,(
% 2.66/0.74    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))) ) | (~spl4_16 | ~spl4_17)),
% 2.66/0.74    inference(resolution,[],[f121,f130])).
% 2.66/0.74  fof(f130,plain,(
% 2.66/0.74    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) ) | ~spl4_17),
% 2.66/0.74    inference(avatar_component_clause,[],[f129])).
% 2.66/0.74  fof(f1054,plain,(
% 2.66/0.74    spl4_83 | ~spl4_22 | ~spl4_58),
% 2.66/0.74    inference(avatar_split_clause,[],[f592,f575,f165,f1052])).
% 2.66/0.74  fof(f575,plain,(
% 2.66/0.74    spl4_58 <=> sK0 = k2_xboole_0(sK2,sK0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.66/0.74  fof(f592,plain,(
% 2.66/0.74    ( ! [X0] : (r1_tarski(X0,sK0) | ~r1_tarski(k4_xboole_0(X0,sK2),sK0)) ) | (~spl4_22 | ~spl4_58)),
% 2.66/0.74    inference(superposition,[],[f166,f576])).
% 2.66/0.74  fof(f576,plain,(
% 2.66/0.74    sK0 = k2_xboole_0(sK2,sK0) | ~spl4_58),
% 2.66/0.74    inference(avatar_component_clause,[],[f575])).
% 2.66/0.74  fof(f697,plain,(
% 2.66/0.74    spl4_64 | ~spl4_27),
% 2.66/0.74    inference(avatar_split_clause,[],[f253,f198,f695])).
% 2.66/0.74  fof(f253,plain,(
% 2.66/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))) ) | ~spl4_27),
% 2.66/0.74    inference(forward_demodulation,[],[f252,f199])).
% 2.66/0.74  fof(f252,plain,(
% 2.66/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6))) ) | ~spl4_27),
% 2.66/0.74    inference(forward_demodulation,[],[f246,f199])).
% 2.66/0.74  fof(f246,plain,(
% 2.66/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X6)) ) | ~spl4_27),
% 2.66/0.74    inference(superposition,[],[f199,f199])).
% 2.66/0.74  fof(f581,plain,(
% 2.66/0.74    spl4_59 | ~spl4_3 | ~spl4_14 | ~spl4_24),
% 2.66/0.74    inference(avatar_split_clause,[],[f226,f186,f112,f68,f579])).
% 2.66/0.74  fof(f68,plain,(
% 2.66/0.74    spl4_3 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.66/0.74  fof(f112,plain,(
% 2.66/0.74    spl4_14 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.66/0.74  fof(f186,plain,(
% 2.66/0.74    spl4_24 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.66/0.74  fof(f226,plain,(
% 2.66/0.74    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X2))) ) | (~spl4_3 | ~spl4_14 | ~spl4_24)),
% 2.66/0.74    inference(subsumption_resolution,[],[f219,f69])).
% 2.66/0.74  fof(f69,plain,(
% 2.66/0.74    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl4_3),
% 2.66/0.74    inference(avatar_component_clause,[],[f68])).
% 2.66/0.74  fof(f219,plain,(
% 2.66/0.74    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X2)) | v1_xboole_0(k1_zfmisc_1(X2))) ) | (~spl4_14 | ~spl4_24)),
% 2.66/0.74    inference(resolution,[],[f187,f113])).
% 2.66/0.74  fof(f113,plain,(
% 2.66/0.74    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_14),
% 2.66/0.74    inference(avatar_component_clause,[],[f112])).
% 2.66/0.74  fof(f187,plain,(
% 2.66/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl4_24),
% 2.66/0.74    inference(avatar_component_clause,[],[f186])).
% 2.66/0.74  fof(f577,plain,(
% 2.66/0.74    spl4_58 | ~spl4_42 | ~spl4_53),
% 2.66/0.74    inference(avatar_split_clause,[],[f508,f490,f329,f575])).
% 2.66/0.74  fof(f329,plain,(
% 2.66/0.74    spl4_42 <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.66/0.74  fof(f490,plain,(
% 2.66/0.74    spl4_53 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.66/0.74  fof(f508,plain,(
% 2.66/0.74    sK0 = k2_xboole_0(sK2,sK0) | (~spl4_42 | ~spl4_53)),
% 2.66/0.74    inference(superposition,[],[f330,f491])).
% 2.66/0.74  fof(f491,plain,(
% 2.66/0.74    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_53),
% 2.66/0.74    inference(avatar_component_clause,[],[f490])).
% 2.66/0.74  fof(f330,plain,(
% 2.66/0.74    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) ) | ~spl4_42),
% 2.66/0.74    inference(avatar_component_clause,[],[f329])).
% 2.66/0.74  fof(f492,plain,(
% 2.66/0.74    spl4_53 | ~spl4_1 | ~spl4_24 | ~spl4_25 | ~spl4_29 | ~spl4_34),
% 2.66/0.74    inference(avatar_split_clause,[],[f274,f267,f228,f190,f186,f60,f490])).
% 2.66/0.74  fof(f60,plain,(
% 2.66/0.74    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.66/0.74  fof(f190,plain,(
% 2.66/0.74    spl4_25 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.66/0.74  fof(f228,plain,(
% 2.66/0.74    spl4_29 <=> k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.66/0.74  fof(f267,plain,(
% 2.66/0.74    spl4_34 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.66/0.74  fof(f274,plain,(
% 2.66/0.74    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_24 | ~spl4_25 | ~spl4_29 | ~spl4_34)),
% 2.66/0.74    inference(forward_demodulation,[],[f273,f240])).
% 2.66/0.74  fof(f240,plain,(
% 2.66/0.74    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_25 | ~spl4_29)),
% 2.66/0.74    inference(subsumption_resolution,[],[f238,f61])).
% 2.66/0.74  fof(f61,plain,(
% 2.66/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_1),
% 2.66/0.74    inference(avatar_component_clause,[],[f60])).
% 2.66/0.74  fof(f238,plain,(
% 2.66/0.74    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl4_25 | ~spl4_29)),
% 2.66/0.74    inference(superposition,[],[f191,f229])).
% 2.66/0.74  fof(f229,plain,(
% 2.66/0.74    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) | ~spl4_29),
% 2.66/0.74    inference(avatar_component_clause,[],[f228])).
% 2.66/0.74  fof(f191,plain,(
% 2.66/0.74    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_25),
% 2.66/0.74    inference(avatar_component_clause,[],[f190])).
% 2.66/0.74  fof(f273,plain,(
% 2.66/0.74    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_24 | ~spl4_34)),
% 2.66/0.74    inference(resolution,[],[f268,f187])).
% 2.66/0.74  fof(f268,plain,(
% 2.66/0.74    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_34),
% 2.66/0.74    inference(avatar_component_clause,[],[f267])).
% 2.66/0.74  fof(f386,plain,(
% 2.66/0.74    spl4_47 | ~spl4_7 | ~spl4_27),
% 2.66/0.74    inference(avatar_split_clause,[],[f249,f198,f84,f384])).
% 2.66/0.74  fof(f84,plain,(
% 2.66/0.74    spl4_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.66/0.74  fof(f249,plain,(
% 2.66/0.74    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))) ) | (~spl4_7 | ~spl4_27)),
% 2.66/0.74    inference(superposition,[],[f85,f199])).
% 2.66/0.74  fof(f85,plain,(
% 2.66/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl4_7),
% 2.66/0.74    inference(avatar_component_clause,[],[f84])).
% 2.66/0.74  fof(f353,plain,(
% 2.66/0.74    spl4_44 | ~spl4_3 | ~spl4_12 | ~spl4_15),
% 2.66/0.74    inference(avatar_split_clause,[],[f144,f116,f104,f68,f351])).
% 2.66/0.74  fof(f104,plain,(
% 2.66/0.74    spl4_12 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.66/0.74  fof(f116,plain,(
% 2.66/0.74    spl4_15 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.66/0.74  fof(f144,plain,(
% 2.66/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl4_3 | ~spl4_12 | ~spl4_15)),
% 2.66/0.74    inference(subsumption_resolution,[],[f143,f69])).
% 2.66/0.74  fof(f143,plain,(
% 2.66/0.74    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl4_12 | ~spl4_15)),
% 2.66/0.74    inference(resolution,[],[f117,f105])).
% 2.66/0.74  fof(f105,plain,(
% 2.66/0.74    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl4_12),
% 2.66/0.74    inference(avatar_component_clause,[],[f104])).
% 2.66/0.74  fof(f117,plain,(
% 2.66/0.74    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl4_15),
% 2.66/0.74    inference(avatar_component_clause,[],[f116])).
% 2.66/0.74  fof(f331,plain,(
% 2.66/0.74    spl4_42 | ~spl4_7 | ~spl4_16),
% 2.66/0.74    inference(avatar_split_clause,[],[f148,f120,f84,f329])).
% 2.66/0.74  fof(f148,plain,(
% 2.66/0.74    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) ) | (~spl4_7 | ~spl4_16)),
% 2.66/0.74    inference(resolution,[],[f121,f85])).
% 2.66/0.74  fof(f289,plain,(
% 2.66/0.74    ~spl4_37 | ~spl4_1 | ~spl4_2 | spl4_30 | ~spl4_35),
% 2.66/0.74    inference(avatar_split_clause,[],[f285,f276,f232,f64,f60,f287])).
% 2.66/0.74  fof(f232,plain,(
% 2.66/0.74    spl4_30 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.66/0.74  fof(f276,plain,(
% 2.66/0.74    spl4_35 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.66/0.74  fof(f285,plain,(
% 2.66/0.74    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | (~spl4_1 | ~spl4_2 | spl4_30 | ~spl4_35)),
% 2.66/0.74    inference(subsumption_resolution,[],[f284,f65])).
% 2.66/0.74  fof(f284,plain,(
% 2.66/0.74    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl4_1 | spl4_30 | ~spl4_35)),
% 2.66/0.74    inference(subsumption_resolution,[],[f283,f61])).
% 2.66/0.74  fof(f283,plain,(
% 2.66/0.74    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl4_30 | ~spl4_35)),
% 2.66/0.74    inference(superposition,[],[f233,f277])).
% 2.66/0.74  fof(f277,plain,(
% 2.66/0.74    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_35),
% 2.66/0.74    inference(avatar_component_clause,[],[f276])).
% 2.66/0.74  fof(f233,plain,(
% 2.66/0.74    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_30),
% 2.66/0.74    inference(avatar_component_clause,[],[f232])).
% 2.66/0.74  fof(f278,plain,(
% 2.66/0.74    spl4_35),
% 2.66/0.74    inference(avatar_split_clause,[],[f56,f276])).
% 2.66/0.74  fof(f56,plain,(
% 2.66/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.66/0.74    inference(cnf_transformation,[],[f30])).
% 2.66/0.74  fof(f30,plain,(
% 2.66/0.74    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.74    inference(flattening,[],[f29])).
% 2.66/0.74  fof(f29,plain,(
% 2.66/0.74    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.66/0.74    inference(ennf_transformation,[],[f17])).
% 2.66/0.74  fof(f17,axiom,(
% 2.66/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.66/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.66/0.74  fof(f269,plain,(
% 2.66/0.74    spl4_34 | ~spl4_1 | ~spl4_21 | ~spl4_29),
% 2.66/0.74    inference(avatar_split_clause,[],[f237,f228,f154,f60,f267])).
% 2.66/0.74  fof(f154,plain,(
% 2.66/0.74    spl4_21 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.66/0.74  fof(f237,plain,(
% 2.66/0.74    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl4_1 | ~spl4_21 | ~spl4_29)),
% 2.66/0.74    inference(subsumption_resolution,[],[f236,f61])).
% 2.66/0.74  fof(f236,plain,(
% 2.66/0.74    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl4_21 | ~spl4_29)),
% 2.66/0.74    inference(superposition,[],[f155,f229])).
% 2.66/0.75  fof(f155,plain,(
% 2.66/0.75    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_21),
% 2.66/0.75    inference(avatar_component_clause,[],[f154])).
% 2.66/0.75  fof(f234,plain,(
% 2.66/0.75    ~spl4_30 | ~spl4_2 | spl4_5 | ~spl4_24),
% 2.66/0.75    inference(avatar_split_clause,[],[f225,f186,f76,f64,f232])).
% 2.66/0.75  fof(f76,plain,(
% 2.66/0.75    spl4_5 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.66/0.75  fof(f225,plain,(
% 2.66/0.75    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | (~spl4_2 | spl4_5 | ~spl4_24)),
% 2.66/0.75    inference(backward_demodulation,[],[f77,f217])).
% 2.66/0.75  fof(f217,plain,(
% 2.66/0.75    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl4_2 | ~spl4_24)),
% 2.66/0.75    inference(resolution,[],[f187,f65])).
% 2.66/0.75  fof(f77,plain,(
% 2.66/0.75    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl4_5),
% 2.66/0.75    inference(avatar_component_clause,[],[f76])).
% 2.66/0.75  fof(f230,plain,(
% 2.66/0.75    spl4_29 | ~spl4_1 | ~spl4_24),
% 2.66/0.75    inference(avatar_split_clause,[],[f216,f186,f60,f228])).
% 2.66/0.75  fof(f216,plain,(
% 2.66/0.75    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) | (~spl4_1 | ~spl4_24)),
% 2.66/0.75    inference(resolution,[],[f187,f61])).
% 2.66/0.75  fof(f200,plain,(
% 2.66/0.75    spl4_27),
% 2.66/0.75    inference(avatar_split_clause,[],[f53,f198])).
% 2.66/0.75  fof(f53,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f7])).
% 2.66/0.75  fof(f7,axiom,(
% 2.66/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.66/0.75  fof(f192,plain,(
% 2.66/0.75    spl4_25),
% 2.66/0.75    inference(avatar_split_clause,[],[f48,f190])).
% 2.66/0.75  fof(f48,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.66/0.75    inference(cnf_transformation,[],[f25])).
% 2.66/0.75  fof(f25,plain,(
% 2.66/0.75    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f16])).
% 2.66/0.75  fof(f16,axiom,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.66/0.75  fof(f188,plain,(
% 2.66/0.75    spl4_24),
% 2.66/0.75    inference(avatar_split_clause,[],[f47,f186])).
% 2.66/0.75  fof(f47,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f24])).
% 2.66/0.75  fof(f24,plain,(
% 2.66/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f13])).
% 2.66/0.75  fof(f13,axiom,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.66/0.75  fof(f167,plain,(
% 2.66/0.75    spl4_22),
% 2.66/0.75    inference(avatar_split_clause,[],[f54,f165])).
% 2.66/0.75  fof(f54,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f26])).
% 2.66/0.75  fof(f26,plain,(
% 2.66/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.66/0.75    inference(ennf_transformation,[],[f8])).
% 2.66/0.75  fof(f8,axiom,(
% 2.66/0.75    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.66/0.75  fof(f156,plain,(
% 2.66/0.75    spl4_21),
% 2.66/0.75    inference(avatar_split_clause,[],[f46,f154])).
% 2.66/0.75  fof(f46,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f23])).
% 2.66/0.75  fof(f23,plain,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f14])).
% 2.66/0.75  fof(f14,axiom,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.66/0.75  fof(f131,plain,(
% 2.66/0.75    spl4_17 | ~spl4_6 | ~spl4_9),
% 2.66/0.75    inference(avatar_split_clause,[],[f125,f92,f80,f129])).
% 2.66/0.75  fof(f80,plain,(
% 2.66/0.75    spl4_6 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.66/0.75  fof(f92,plain,(
% 2.66/0.75    spl4_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.66/0.75  fof(f125,plain,(
% 2.66/0.75    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) ) | (~spl4_6 | ~spl4_9)),
% 2.66/0.75    inference(superposition,[],[f81,f93])).
% 2.66/0.75  fof(f93,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_9),
% 2.66/0.75    inference(avatar_component_clause,[],[f92])).
% 2.66/0.75  fof(f81,plain,(
% 2.66/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl4_6),
% 2.66/0.75    inference(avatar_component_clause,[],[f80])).
% 2.66/0.75  fof(f122,plain,(
% 2.66/0.75    spl4_16),
% 2.66/0.75    inference(avatar_split_clause,[],[f45,f120])).
% 2.66/0.75  fof(f45,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.66/0.75    inference(cnf_transformation,[],[f22])).
% 2.66/0.75  fof(f22,plain,(
% 2.66/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.66/0.75    inference(ennf_transformation,[],[f2])).
% 2.66/0.75  fof(f2,axiom,(
% 2.66/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.66/0.75  fof(f118,plain,(
% 2.66/0.75    spl4_15),
% 2.66/0.75    inference(avatar_split_clause,[],[f44,f116])).
% 2.66/0.75  fof(f44,plain,(
% 2.66/0.75    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f21])).
% 2.66/0.75  fof(f21,plain,(
% 2.66/0.75    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f12])).
% 2.66/0.75  fof(f12,axiom,(
% 2.66/0.75    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.66/0.75  fof(f114,plain,(
% 2.66/0.75    spl4_14),
% 2.66/0.75    inference(avatar_split_clause,[],[f43,f112])).
% 2.66/0.75  fof(f43,plain,(
% 2.66/0.75    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f21])).
% 2.66/0.75  fof(f110,plain,(
% 2.66/0.75    spl4_13),
% 2.66/0.75    inference(avatar_split_clause,[],[f58,f108])).
% 2.66/0.75  fof(f58,plain,(
% 2.66/0.75    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(equality_resolution,[],[f49])).
% 2.66/0.75  fof(f49,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.66/0.75    inference(cnf_transformation,[],[f11])).
% 2.66/0.75  fof(f11,axiom,(
% 2.66/0.75    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.66/0.75  fof(f106,plain,(
% 2.66/0.75    spl4_12),
% 2.66/0.75    inference(avatar_split_clause,[],[f57,f104])).
% 2.66/0.75  fof(f57,plain,(
% 2.66/0.75    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(equality_resolution,[],[f50])).
% 2.66/0.75  fof(f50,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.66/0.75    inference(cnf_transformation,[],[f11])).
% 2.66/0.75  fof(f94,plain,(
% 2.66/0.75    spl4_9),
% 2.66/0.75    inference(avatar_split_clause,[],[f39,f92])).
% 2.66/0.75  fof(f39,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f1])).
% 2.66/0.75  fof(f1,axiom,(
% 2.66/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.66/0.75  fof(f90,plain,(
% 2.66/0.75    spl4_8),
% 2.66/0.75    inference(avatar_split_clause,[],[f38,f88])).
% 2.66/0.75  fof(f38,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f9])).
% 2.66/0.75  fof(f9,axiom,(
% 2.66/0.75    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.66/0.75  fof(f86,plain,(
% 2.66/0.75    spl4_7),
% 2.66/0.75    inference(avatar_split_clause,[],[f37,f84])).
% 2.66/0.75  fof(f37,plain,(
% 2.66/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f5])).
% 2.66/0.75  fof(f5,axiom,(
% 2.66/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.66/0.75  fof(f82,plain,(
% 2.66/0.75    spl4_6),
% 2.66/0.75    inference(avatar_split_clause,[],[f36,f80])).
% 2.66/0.75  fof(f36,plain,(
% 2.66/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f10])).
% 2.66/0.75  fof(f10,axiom,(
% 2.66/0.75    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.66/0.75  fof(f78,plain,(
% 2.66/0.75    ~spl4_5),
% 2.66/0.75    inference(avatar_split_clause,[],[f32,f76])).
% 2.66/0.75  fof(f32,plain,(
% 2.66/0.75    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.66/0.75    inference(cnf_transformation,[],[f20])).
% 2.66/0.75  fof(f20,plain,(
% 2.66/0.75    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f19])).
% 2.66/0.75  fof(f19,negated_conjecture,(
% 2.66/0.75    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.66/0.75    inference(negated_conjecture,[],[f18])).
% 2.66/0.75  fof(f18,conjecture,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 2.66/0.75  fof(f74,plain,(
% 2.66/0.75    spl4_4),
% 2.66/0.75    inference(avatar_split_clause,[],[f35,f72])).
% 2.66/0.75  fof(f35,plain,(
% 2.66/0.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f4])).
% 2.66/0.75  fof(f4,axiom,(
% 2.66/0.75    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.66/0.75  fof(f70,plain,(
% 2.66/0.75    spl4_3),
% 2.66/0.75    inference(avatar_split_clause,[],[f34,f68])).
% 2.66/0.75  fof(f34,plain,(
% 2.66/0.75    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f15])).
% 2.66/0.75  fof(f15,axiom,(
% 2.66/0.75    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.66/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.66/0.75  fof(f66,plain,(
% 2.66/0.75    spl4_2),
% 2.66/0.75    inference(avatar_split_clause,[],[f33,f64])).
% 2.66/0.75  fof(f33,plain,(
% 2.66/0.75    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.66/0.75    inference(cnf_transformation,[],[f20])).
% 2.66/0.75  fof(f62,plain,(
% 2.66/0.75    spl4_1),
% 2.66/0.75    inference(avatar_split_clause,[],[f31,f60])).
% 2.66/0.75  fof(f31,plain,(
% 2.66/0.75    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.66/0.75    inference(cnf_transformation,[],[f20])).
% 2.66/0.75  % SZS output end Proof for theBenchmark
% 2.66/0.75  % (9221)------------------------------
% 2.66/0.75  % (9221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.75  % (9221)Termination reason: Refutation
% 2.66/0.75  
% 2.66/0.75  % (9221)Memory used [KB]: 13304
% 2.66/0.75  % (9221)Time elapsed: 0.247 s
% 2.66/0.75  % (9221)------------------------------
% 2.66/0.75  % (9221)------------------------------
% 2.66/0.75  % (9211)Success in time 0.386 s
%------------------------------------------------------------------------------
