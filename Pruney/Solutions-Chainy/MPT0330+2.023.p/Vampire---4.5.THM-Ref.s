%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 208 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :    7
%              Number of atoms          :  287 ( 499 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f45,f49,f53,f57,f61,f65,f69,f76,f87,f92,f108,f112,f155,f219,f268,f288,f341,f833,f1163,f1179,f2537,f2601,f3125,f3127])).

fof(f3127,plain,
    ( spl6_106
    | ~ spl6_307 ),
    inference(avatar_contradiction_clause,[],[f3126])).

fof(f3126,plain,
    ( $false
    | spl6_106
    | ~ spl6_307 ),
    inference(subsumption_resolution,[],[f832,f2600])).

fof(f2600,plain,
    ( ! [X78,X79] : r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5)))
    | ~ spl6_307 ),
    inference(avatar_component_clause,[],[f2599])).

fof(f2599,plain,
    ( spl6_307
  <=> ! [X79,X78] : r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_307])])).

fof(f832,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_106 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl6_106
  <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f3125,plain,
    ( spl6_105
    | ~ spl6_291 ),
    inference(avatar_contradiction_clause,[],[f3115])).

fof(f3115,plain,
    ( $false
    | spl6_105
    | ~ spl6_291 ),
    inference(resolution,[],[f2536,f828])).

fof(f828,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_105 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl6_105
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f2536,plain,
    ( ! [X39,X38] : r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38)))
    | ~ spl6_291 ),
    inference(avatar_component_clause,[],[f2535])).

fof(f2535,plain,
    ( spl6_291
  <=> ! [X38,X39] : r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_291])])).

fof(f2601,plain,
    ( spl6_307
    | ~ spl6_8
    | ~ spl6_129 ),
    inference(avatar_split_clause,[],[f2392,f1177,f59,f2599])).

fof(f59,plain,
    ( spl6_8
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1177,plain,
    ( spl6_129
  <=> ! [X20,X19] : r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f2392,plain,
    ( ! [X78,X79] : r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5)))
    | ~ spl6_8
    | ~ spl6_129 ),
    inference(superposition,[],[f1178,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f1178,plain,
    ( ! [X19,X20] : r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5))))
    | ~ spl6_129 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f2537,plain,
    ( spl6_291
    | ~ spl6_8
    | ~ spl6_125 ),
    inference(avatar_split_clause,[],[f2376,f1161,f59,f2535])).

fof(f1161,plain,
    ( spl6_125
  <=> ! [X11,X12] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f2376,plain,
    ( ! [X39,X38] : r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38)))
    | ~ spl6_8
    | ~ spl6_125 ),
    inference(superposition,[],[f1162,f60])).

fof(f1162,plain,
    ( ! [X12,X11] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12))
    | ~ spl6_125 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1179,plain,
    ( spl6_129
    | ~ spl6_7
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f1092,f266,f55,f1177])).

fof(f55,plain,
    ( spl6_7
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f266,plain,
    ( spl6_41
  <=> ! [X5,X4] : r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1092,plain,
    ( ! [X19,X20] : r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5))))
    | ~ spl6_7
    | ~ spl6_41 ),
    inference(superposition,[],[f267,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f267,plain,
    ( ! [X4,X5] : r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1163,plain,
    ( spl6_125
    | ~ spl6_7
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f1088,f339,f55,f1161])).

fof(f339,plain,
    ( spl6_53
  <=> ! [X7,X6] : r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f1088,plain,
    ( ! [X12,X11] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12))
    | ~ spl6_7
    | ~ spl6_53 ),
    inference(superposition,[],[f340,f56])).

fof(f340,plain,
    ( ! [X6,X7] : r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f339])).

fof(f833,plain,
    ( ~ spl6_105
    | ~ spl6_106
    | spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f817,f67,f28,f830,f826])).

fof(f28,plain,
    ( spl6_1
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f67,plain,
    ( spl6_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f817,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1
    | ~ spl6_10 ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f341,plain,
    ( spl6_53
    | ~ spl6_16
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f328,f286,f106,f339])).

fof(f106,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f286,plain,
    ( spl6_44
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f328,plain,
    ( ! [X6,X7] : r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7))
    | ~ spl6_16
    | ~ spl6_44 ),
    inference(resolution,[],[f287,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl6_44
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f278,f89,f63,f286])).

fof(f63,plain,
    ( spl6_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f89,plain,
    ( spl6_13
  <=> k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(superposition,[],[f64,f91])).

fof(f91,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f268,plain,
    ( spl6_41
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f258,f217,f152,f266])).

fof(f152,plain,
    ( spl6_24
  <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f217,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X0)
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f258,plain,
    ( ! [X4,X5] : r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(resolution,[],[f218,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl6_33
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f209,f84,f63,f217])).

fof(f84,plain,
    ( spl6_12
  <=> k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(superposition,[],[f64,f86])).

fof(f86,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f155,plain,
    ( spl6_24
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f140,f110,f47,f152])).

fof(f47,plain,
    ( spl6_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f110,plain,
    ( spl6_17
  <=> ! [X3,X5,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f140,plain,
    ( ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X5,k2_xboole_0(X4,X3)))
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(superposition,[],[f111,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f111,plain,
    ( ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl6_17
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f102,f73,f63,f110])).

fof(f73,plain,
    ( spl6_11
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f102,plain,
    ( ! [X4,X5,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f108,plain,
    ( spl6_16
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f101,f63,f43,f106])).

fof(f43,plain,
    ( spl6_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,
    ( ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f92,plain,
    ( spl6_13
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f80,f51,f38,f89])).

fof(f38,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f51,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f80,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f87,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f79,f51,f33,f84])).

fof(f33,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f79,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f76,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f71,f47,f43,f73])).

fof(f71,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(superposition,[],[f44,f48])).

fof(f69,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f65,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f61,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f57,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f36,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f19,f28])).

fof(f19,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (4157)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (4158)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (4160)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (4156)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (4152)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (4154)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.44  % (4155)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.46  % (4153)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.46  % (4162)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.46  % (4161)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.48  % (4159)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.48  % (4163)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.50  % (4157)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f3128,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f31,f36,f41,f45,f49,f53,f57,f61,f65,f69,f76,f87,f92,f108,f112,f155,f219,f268,f288,f341,f833,f1163,f1179,f2537,f2601,f3125,f3127])).
% 0.21/0.50  fof(f3127,plain,(
% 0.21/0.50    spl6_106 | ~spl6_307),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f3126])).
% 0.21/0.50  fof(f3126,plain,(
% 0.21/0.50    $false | (spl6_106 | ~spl6_307)),
% 0.21/0.50    inference(subsumption_resolution,[],[f832,f2600])).
% 0.21/0.50  fof(f2600,plain,(
% 0.21/0.50    ( ! [X78,X79] : (r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5)))) ) | ~spl6_307),
% 0.21/0.50    inference(avatar_component_clause,[],[f2599])).
% 0.21/0.50  fof(f2599,plain,(
% 0.21/0.50    spl6_307 <=> ! [X79,X78] : r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_307])])).
% 0.21/0.50  fof(f832,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_106),
% 0.21/0.50    inference(avatar_component_clause,[],[f830])).
% 0.21/0.50  fof(f830,plain,(
% 0.21/0.50    spl6_106 <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 0.21/0.50  fof(f3125,plain,(
% 0.21/0.50    spl6_105 | ~spl6_291),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f3115])).
% 0.21/0.50  fof(f3115,plain,(
% 0.21/0.50    $false | (spl6_105 | ~spl6_291)),
% 0.21/0.50    inference(resolution,[],[f2536,f828])).
% 0.21/0.50  fof(f828,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_105),
% 0.21/0.50    inference(avatar_component_clause,[],[f826])).
% 0.21/0.50  fof(f826,plain,(
% 0.21/0.50    spl6_105 <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 0.21/0.50  fof(f2536,plain,(
% 0.21/0.50    ( ! [X39,X38] : (r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38)))) ) | ~spl6_291),
% 0.21/0.50    inference(avatar_component_clause,[],[f2535])).
% 0.21/0.50  fof(f2535,plain,(
% 0.21/0.50    spl6_291 <=> ! [X38,X39] : r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_291])])).
% 0.21/0.50  fof(f2601,plain,(
% 0.21/0.50    spl6_307 | ~spl6_8 | ~spl6_129),
% 0.21/0.50    inference(avatar_split_clause,[],[f2392,f1177,f59,f2599])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl6_8 <=> ! [X1,X0,X2] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f1177,plain,(
% 0.21/0.50    spl6_129 <=> ! [X20,X19] : r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 0.21/0.50  fof(f2392,plain,(
% 0.21/0.50    ( ! [X78,X79] : (r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(X78,sK4),k2_xboole_0(X79,sK5)))) ) | (~spl6_8 | ~spl6_129)),
% 0.21/0.50    inference(superposition,[],[f1178,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f1178,plain,(
% 0.21/0.50    ( ! [X19,X20] : (r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5))))) ) | ~spl6_129),
% 0.21/0.50    inference(avatar_component_clause,[],[f1177])).
% 0.21/0.50  fof(f2537,plain,(
% 0.21/0.50    spl6_291 | ~spl6_8 | ~spl6_125),
% 0.21/0.50    inference(avatar_split_clause,[],[f2376,f1161,f59,f2535])).
% 0.21/0.50  fof(f1161,plain,(
% 0.21/0.50    spl6_125 <=> ! [X11,X12] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).
% 0.21/0.50  fof(f2376,plain,(
% 0.21/0.50    ( ! [X39,X38] : (r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X39),k2_xboole_0(sK3,X38)))) ) | (~spl6_8 | ~spl6_125)),
% 0.21/0.50    inference(superposition,[],[f1162,f60])).
% 0.21/0.50  fof(f1162,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12))) ) | ~spl6_125),
% 0.21/0.50    inference(avatar_component_clause,[],[f1161])).
% 0.21/0.50  fof(f1179,plain,(
% 0.21/0.50    spl6_129 | ~spl6_7 | ~spl6_41),
% 0.21/0.50    inference(avatar_split_clause,[],[f1092,f266,f55,f1177])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl6_7 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    spl6_41 <=> ! [X5,X4] : r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.50  fof(f1092,plain,(
% 0.21/0.50    ( ! [X19,X20] : (r1_tarski(sK1,k2_xboole_0(X20,k2_zfmisc_1(sK4,k2_xboole_0(X19,sK5))))) ) | (~spl6_7 | ~spl6_41)),
% 0.21/0.50    inference(superposition,[],[f267,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5))))) ) | ~spl6_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f266])).
% 0.21/0.50  fof(f1163,plain,(
% 0.21/0.50    spl6_125 | ~spl6_7 | ~spl6_53),
% 0.21/0.50    inference(avatar_split_clause,[],[f1088,f339,f55,f1161])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    spl6_53 <=> ! [X7,X6] : r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.50  fof(f1088,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X11)),X12))) ) | (~spl6_7 | ~spl6_53)),
% 0.21/0.50    inference(superposition,[],[f340,f56])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ( ! [X6,X7] : (r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7))) ) | ~spl6_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f339])).
% 0.21/0.50  fof(f833,plain,(
% 0.21/0.50    ~spl6_105 | ~spl6_106 | spl6_1 | ~spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f817,f67,f28,f830,f826])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    spl6_1 <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl6_10 <=> ! [X1,X0,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f817,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | (spl6_1 | ~spl6_10)),
% 0.21/0.50    inference(resolution,[],[f68,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f28])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    spl6_53 | ~spl6_16 | ~spl6_44),
% 0.21/0.50    inference(avatar_split_clause,[],[f328,f286,f106,f339])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl6_16 <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    spl6_44 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ( ! [X6,X7] : (r1_tarski(sK0,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK2,sK3),X6),X7))) ) | (~spl6_16 | ~spl6_44)),
% 0.21/0.50    inference(resolution,[],[f287,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | ~spl6_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f286])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl6_44 | ~spl6_9 | ~spl6_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f278,f89,f63,f286])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl6_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl6_13 <=> k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | (~spl6_9 | ~spl6_13)),
% 0.21/0.50    inference(superposition,[],[f64,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    spl6_41 | ~spl6_24 | ~spl6_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f258,f217,f152,f266])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl6_24 <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(X2,k2_xboole_0(X1,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl6_33 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X0) | r1_tarski(sK1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r1_tarski(sK1,k2_xboole_0(X4,k2_xboole_0(X5,k2_zfmisc_1(sK4,sK5))))) ) | (~spl6_24 | ~spl6_33)),
% 0.21/0.50    inference(resolution,[],[f218,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | ~spl6_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X0) | r1_tarski(sK1,X0)) ) | ~spl6_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f217])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    spl6_33 | ~spl6_9 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f209,f84,f63,f217])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl6_12 <=> k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X0) | r1_tarski(sK1,X0)) ) | (~spl6_9 | ~spl6_12)),
% 0.21/0.50    inference(superposition,[],[f64,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl6_24 | ~spl6_5 | ~spl6_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f110,f47,f152])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl6_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl6_17 <=> ! [X3,X5,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X5,k2_xboole_0(X4,X3)))) ) | (~spl6_5 | ~spl6_17)),
% 0.21/0.50    inference(superposition,[],[f111,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))) ) | ~spl6_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl6_17 | ~spl6_9 | ~spl6_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f73,f63,f110])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl6_11 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X5)))) ) | (~spl6_9 | ~spl6_11)),
% 0.21/0.50    inference(resolution,[],[f64,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl6_16 | ~spl6_4 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f63,f43,f106])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl6_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ) | (~spl6_4 | ~spl6_9)),
% 0.21/0.50    inference(resolution,[],[f64,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f43])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl6_13 | ~spl6_3 | ~spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f80,f51,f38,f89])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    spl6_3 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl6_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) | (~spl6_3 | ~spl6_6)),
% 0.21/0.50    inference(resolution,[],[f52,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f38])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl6_12 | ~spl6_2 | ~spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f79,f51,f33,f84])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) | (~spl6_2 | ~spl6_6)),
% 0.21/0.50    inference(resolution,[],[f52,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f33])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl6_11 | ~spl6_4 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f47,f43,f73])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(superposition,[],[f44,f48])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f67])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f51])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f43])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f28])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4157)------------------------------
% 0.21/0.50  % (4157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4157)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4157)Memory used [KB]: 12792
% 0.21/0.50  % (4157)Time elapsed: 0.100 s
% 0.21/0.50  % (4157)------------------------------
% 0.21/0.50  % (4157)------------------------------
% 0.21/0.51  % (4151)Success in time 0.146 s
%------------------------------------------------------------------------------
