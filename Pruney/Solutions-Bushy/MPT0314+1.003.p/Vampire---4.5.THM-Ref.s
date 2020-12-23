%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0314+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:44 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 178 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :    6
%              Number of atoms          :  274 ( 431 expanded)
%              Number of equality atoms :   84 ( 142 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f67,f71,f85,f94,f110,f114,f118,f141,f184,f188,f391,f478,f547,f2307,f2687,f3358,f4453,f5239,f7065,f7169])).

fof(f7169,plain,
    ( spl6_10
    | ~ spl6_166 ),
    inference(avatar_contradiction_clause,[],[f7088])).

fof(f7088,plain,
    ( $false
    | spl6_10
    | ~ spl6_166 ),
    inference(unit_resulting_resolution,[],[f84,f7064])).

fof(f7064,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k2_zfmisc_1(X4,k4_xboole_0(X5,X6)),k2_zfmisc_1(k4_xboole_0(X4,X7),X5)) = k4_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6))
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f7063])).

fof(f7063,plain,
    ( spl6_166
  <=> ! [X5,X7,X4,X6] : k2_xboole_0(k2_zfmisc_1(X4,k4_xboole_0(X5,X6)),k2_zfmisc_1(k4_xboole_0(X4,X7),X5)) = k4_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f84,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_10
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f7065,plain,
    ( spl6_166
    | ~ spl6_16
    | ~ spl6_45
    | ~ spl6_111
    | ~ spl6_126 ),
    inference(avatar_split_clause,[],[f5301,f5237,f4451,f545,f116,f7063])).

fof(f116,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f545,plain,
    ( spl6_45
  <=> ! [X1,X3,X0,X2] : k4_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(X3,k2_zfmisc_1(X2,X1))) = k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,X1),X3),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f4451,plain,
    ( spl6_111
  <=> ! [X9,X11,X8,X10] : k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) = k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f5237,plain,
    ( spl6_126
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f5301,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k2_zfmisc_1(X4,k4_xboole_0(X5,X6)),k2_zfmisc_1(k4_xboole_0(X4,X7),X5)) = k4_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6))
    | ~ spl6_16
    | ~ spl6_45
    | ~ spl6_111
    | ~ spl6_126 ),
    inference(backward_demodulation,[],[f566,f5259])).

fof(f5259,plain,
    ( ! [X6,X8,X7,X9] : k4_xboole_0(k2_zfmisc_1(X6,X7),k2_zfmisc_1(X8,X9)) = k4_xboole_0(k2_zfmisc_1(X6,X7),k3_xboole_0(k2_zfmisc_1(X6,X9),k2_zfmisc_1(X8,X7)))
    | ~ spl6_111
    | ~ spl6_126 ),
    inference(superposition,[],[f5238,f4452])).

fof(f4452,plain,
    ( ! [X10,X8,X11,X9] : k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) = k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f4451])).

fof(f5238,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl6_126 ),
    inference(avatar_component_clause,[],[f5237])).

fof(f566,plain,
    ( ! [X6,X4,X7,X5] : k4_xboole_0(k2_zfmisc_1(X4,X5),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X7,X5))) = k2_xboole_0(k2_zfmisc_1(X4,k4_xboole_0(X5,X6)),k2_zfmisc_1(k4_xboole_0(X4,X7),X5))
    | ~ spl6_16
    | ~ spl6_45 ),
    inference(superposition,[],[f546,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f546,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(X3,k2_zfmisc_1(X2,X1))) = k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,X1),X3),k2_zfmisc_1(k4_xboole_0(X0,X2),X1))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f545])).

fof(f5239,plain,
    ( spl6_126
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_97 ),
    inference(avatar_split_clause,[],[f3660,f3356,f108,f92,f5237])).

fof(f92,plain,
    ( spl6_12
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f108,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f3356,plain,
    ( spl6_97
  <=> ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f3660,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f3372,f93])).

fof(f93,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f3372,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))
    | ~ spl6_14
    | ~ spl6_97 ),
    inference(superposition,[],[f109,f3357])).

fof(f3357,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6)
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f3356])).

fof(f109,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f4453,plain,
    ( spl6_111
    | ~ spl6_17
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f401,f389,f139,f4451])).

fof(f139,plain,
    ( spl6_17
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f389,plain,
    ( spl6_36
  <=> ! [X1,X3,X0,X2] : k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f401,plain,
    ( ! [X10,X8,X11,X9] : k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) = k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10))
    | ~ spl6_17
    | ~ spl6_36 ),
    inference(superposition,[],[f390,f140])).

fof(f140,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f390,plain,
    ( ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k3_xboole_0(X1,X0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f389])).

fof(f3358,plain,
    ( spl6_97
    | ~ spl6_8
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f2713,f2685,f69,f3356])).

fof(f69,plain,
    ( spl6_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2685,plain,
    ( spl6_94
  <=> ! [X60,X59] :
        ( r2_hidden(sK5(X60,X60,k1_xboole_0),X59)
        | k1_xboole_0 = k4_xboole_0(X60,X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f2713,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6)
    | ~ spl6_8
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f2698,f2686])).

fof(f2686,plain,
    ( ! [X59,X60] :
        ( r2_hidden(sK5(X60,X60,k1_xboole_0),X59)
        | k1_xboole_0 = k4_xboole_0(X60,X60) )
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f2685])).

fof(f2698,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 = k4_xboole_0(X6,X6)
        | ~ r2_hidden(sK5(X6,X6,k1_xboole_0),k4_xboole_0(X7,X8)) )
    | ~ spl6_8
    | ~ spl6_94 ),
    inference(resolution,[],[f2686,f70])).

fof(f70,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f2687,plain,
    ( spl6_94
    | ~ spl6_12
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f2335,f2305,f92,f2685])).

fof(f2305,plain,
    ( spl6_86
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X0) = X1
        | r2_hidden(sK5(X0,X0,X1),k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f2335,plain,
    ( ! [X59,X60] :
        ( r2_hidden(sK5(X60,X60,k1_xboole_0),X59)
        | k1_xboole_0 = k4_xboole_0(X60,X60) )
    | ~ spl6_12
    | ~ spl6_86 ),
    inference(superposition,[],[f2306,f93])).

fof(f2306,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK5(X0,X0,X1),k2_xboole_0(X1,X2))
        | k4_xboole_0(X0,X0) = X1 )
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f2305])).

fof(f2307,plain,
    ( spl6_86
    | ~ spl6_7
    | ~ spl6_23
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f499,f476,f186,f65,f2305])).

fof(f65,plain,
    ( spl6_7
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f186,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK5(X0,X1,X2),X1)
        | r2_hidden(sK5(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f476,plain,
    ( spl6_41
  <=> ! [X9,X11,X8,X10] :
        ( r2_hidden(sK5(X8,X9,X10),X8)
        | k4_xboole_0(X8,X9) = X10
        | r2_hidden(sK5(X8,X9,X10),k2_xboole_0(X10,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f499,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,X0) = X1
        | r2_hidden(sK5(X0,X0,X1),k2_xboole_0(X1,X2)) )
    | ~ spl6_7
    | ~ spl6_23
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f498,f66])).

fof(f66,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f498,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,X0) = X1
        | r2_hidden(sK5(X0,X0,X1),k2_xboole_0(X1,X2))
        | r2_hidden(sK5(X0,X0,X1),X1) )
    | ~ spl6_23
    | ~ spl6_41 ),
    inference(duplicate_literal_removal,[],[f483])).

fof(f483,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,X0) = X1
        | r2_hidden(sK5(X0,X0,X1),k2_xboole_0(X1,X2))
        | r2_hidden(sK5(X0,X0,X1),X1)
        | k4_xboole_0(X0,X0) = X1 )
    | ~ spl6_23
    | ~ spl6_41 ),
    inference(resolution,[],[f477,f187])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(X0,X1,X2),X1)
        | r2_hidden(sK5(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f186])).

fof(f477,plain,
    ( ! [X10,X8,X11,X9] :
        ( r2_hidden(sK5(X8,X9,X10),X8)
        | k4_xboole_0(X8,X9) = X10
        | r2_hidden(sK5(X8,X9,X10),k2_xboole_0(X10,X11)) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f476])).

fof(f547,plain,
    ( spl6_45
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f130,f112,f108,f545])).

fof(f112,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f130,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(X3,k2_zfmisc_1(X2,X1))) = k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,X1),X3),k2_zfmisc_1(k4_xboole_0(X0,X2),X1))
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(superposition,[],[f109,f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f478,plain,
    ( spl6_41
    | ~ spl6_7
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f207,f182,f65,f476])).

fof(f182,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK5(X0,X1,X2),X0)
        | r2_hidden(sK5(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f207,plain,
    ( ! [X10,X8,X11,X9] :
        ( r2_hidden(sK5(X8,X9,X10),X8)
        | k4_xboole_0(X8,X9) = X10
        | r2_hidden(sK5(X8,X9,X10),k2_xboole_0(X10,X11)) )
    | ~ spl6_7
    | ~ spl6_22 ),
    inference(resolution,[],[f183,f66])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK5(X0,X1,X2),X2)
        | r2_hidden(sK5(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f391,plain,
    ( spl6_36
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f148,f139,f53,f389])).

fof(f53,plain,
    ( spl6_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f148,plain,
    ( ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k3_xboole_0(X1,X0))
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(superposition,[],[f140,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f188,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f29,f186])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f184,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f28,f182])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f141,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f33,f139])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f118,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f20,f116])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f114,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f19,f112])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f110,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f18,f108])).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f94,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f76,f57,f45,f92])).

fof(f45,plain,
    ( spl6_2
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f57,plain,
    ( spl6_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f76,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(superposition,[],[f58,f46])).

fof(f46,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f58,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f85,plain,
    ( ~ spl6_10
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f79,f57,f49,f83])).

fof(f49,plain,
    ( spl6_3
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f79,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))
    | spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f50,f58])).

fof(f50,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f71,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f59,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f17,f57])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f16,f53])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f13,f49])).

fof(f13,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

%------------------------------------------------------------------------------
