%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t134_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  372 ( 917 expanded)
%              Number of leaves         :   84 ( 377 expanded)
%              Depth                    :    7
%              Number of atoms          : 1001 (2341 expanded)
%              Number of equality atoms :  108 ( 481 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f814,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f66,f73,f80,f116,f121,f135,f139,f153,f158,f160,f173,f177,f191,f196,f209,f218,f225,f240,f245,f259,f263,f277,f281,f295,f296,f302,f303,f318,f319,f323,f342,f367,f382,f387,f403,f407,f415,f416,f417,f419,f432,f437,f451,f455,f459,f473,f475,f480,f494,f499,f529,f530,f532,f534,f545,f552,f557,f569,f576,f587,f589,f595,f596,f598,f625,f628,f665,f683,f685,f728,f747,f755,f756,f757,f759,f787,f795,f802,f811,f813])).

fof(f813,plain,
    ( ~ spl6_44
    | spl6_47
    | ~ spl6_106 ),
    inference(avatar_contradiction_clause,[],[f812])).

fof(f812,plain,
    ( $false
    | ~ spl6_44
    | ~ spl6_47
    | ~ spl6_106 ),
    inference(subsumption_resolution,[],[f808,f276])).

fof(f276,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_47
  <=> ~ r2_hidden(sK5(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f808,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl6_44
    | ~ spl6_106 ),
    inference(resolution,[],[f794,f267])).

fof(f267,plain,
    ( r2_hidden(sK5(sK2,sK0),sK2)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_44
  <=> r2_hidden(sK5(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f794,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK2)
        | r2_hidden(X7,sK0) )
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl6_106
  <=> ! [X7] :
        ( ~ r2_hidden(X7,sK2)
        | r2_hidden(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f811,plain,
    ( spl6_29
    | ~ spl6_30
    | ~ spl6_106 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_106 ),
    inference(subsumption_resolution,[],[f807,f184])).

fof(f184,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK5(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f807,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_30
    | ~ spl6_106 ),
    inference(resolution,[],[f794,f187])).

fof(f187,plain,
    ( r2_hidden(sK5(sK0,sK2),sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_30
  <=> r2_hidden(sK5(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f802,plain,
    ( spl6_108
    | spl6_41
    | spl6_43
    | spl6_63
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f777,f663,f356,f257,f251,f800])).

fof(f800,plain,
    ( spl6_108
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f251,plain,
    ( spl6_41
  <=> ~ r2_hidden(sK5(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f257,plain,
    ( spl6_43
  <=> ~ r2_hidden(sK5(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f356,plain,
    ( spl6_63
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f663,plain,
    ( spl6_100
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK3)
        | r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f777,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl6_41
    | ~ spl6_43
    | ~ spl6_63
    | ~ spl6_100 ),
    inference(backward_demodulation,[],[f261,f681])).

fof(f681,plain,
    ( r2_hidden(sK4(sK3),sK1)
    | ~ spl6_63
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f674,f357])).

fof(f357,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f356])).

fof(f674,plain,
    ( r2_hidden(sK4(sK3),sK1)
    | k1_xboole_0 = sK3
    | ~ spl6_100 ),
    inference(resolution,[],[f664,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',t7_xboole_0)).

fof(f664,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK3)
        | r2_hidden(X3,sK1) )
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f663])).

fof(f261,plain,
    ( sK1 = sK3
    | ~ spl6_41
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f260,f258])).

fof(f258,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f257])).

fof(f260,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | sK1 = sK3
    | ~ spl6_41 ),
    inference(resolution,[],[f252,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',t2_tarski)).

fof(f252,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK3)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f251])).

fof(f795,plain,
    ( spl6_106
    | spl6_94
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f737,f543,f564,f793])).

fof(f564,plain,
    ( spl6_94
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f543,plain,
    ( spl6_92
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f737,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X7,sK0) )
    | ~ spl6_92 ),
    inference(resolution,[],[f548,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',l54_zfmisc_1)).

fof(f548,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_92 ),
    inference(superposition,[],[f37,f544])).

fof(f544,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f543])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f787,plain,
    ( spl6_4
    | spl6_41
    | spl6_43 ),
    inference(avatar_split_clause,[],[f261,f257,f251,f55])).

fof(f55,plain,
    ( spl6_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f759,plain,
    ( spl6_61
    | ~ spl6_104 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl6_61
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f749,f351])).

fof(f351,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_61
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f749,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_104 ),
    inference(resolution,[],[f746,f29])).

fof(f746,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl6_104
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f757,plain,
    ( ~ spl6_30
    | ~ spl6_104 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | ~ spl6_30
    | ~ spl6_104 ),
    inference(resolution,[],[f746,f187])).

fof(f756,plain,
    ( ~ spl6_44
    | ~ spl6_104 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | ~ spl6_44
    | ~ spl6_104 ),
    inference(resolution,[],[f746,f267])).

fof(f755,plain,
    ( ~ spl6_70
    | ~ spl6_104 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | ~ spl6_70
    | ~ spl6_104 ),
    inference(resolution,[],[f746,f393])).

fof(f393,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),sK2)
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl6_70
  <=> r2_hidden(sK5(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f747,plain,
    ( spl6_104
    | spl6_100
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f731,f71,f663,f745])).

fof(f71,plain,
    ( spl6_8
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f731,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X4,sK1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f330,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f330,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2) )
    | ~ spl6_8 ),
    inference(superposition,[],[f37,f72])).

fof(f72,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f728,plain,
    ( ~ spl6_103
    | spl6_69
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f698,f567,f380,f726])).

fof(f726,plain,
    ( spl6_103
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f380,plain,
    ( spl6_69
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f567,plain,
    ( spl6_96
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f698,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK2),sK0)
    | ~ spl6_69
    | ~ spl6_96 ),
    inference(resolution,[],[f568,f381])).

fof(f381,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK2),sK2)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f380])).

fof(f568,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f567])).

fof(f685,plain,
    ( ~ spl6_40
    | spl6_43
    | ~ spl6_100 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl6_40
    | ~ spl6_43
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f679,f258])).

fof(f679,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl6_40
    | ~ spl6_100 ),
    inference(resolution,[],[f664,f249])).

fof(f249,plain,
    ( r2_hidden(sK5(sK3,sK1),sK3)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl6_40
  <=> r2_hidden(sK5(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f683,plain,
    ( spl6_37
    | ~ spl6_38
    | ~ spl6_100 ),
    inference(avatar_contradiction_clause,[],[f682])).

fof(f682,plain,
    ( $false
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f678,f233])).

fof(f233,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_37
  <=> ~ r2_hidden(sK5(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f678,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_38
    | ~ spl6_100 ),
    inference(resolution,[],[f664,f236])).

fof(f236,plain,
    ( r2_hidden(sK5(sK1,sK3),sK3)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl6_38
  <=> r2_hidden(sK5(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f665,plain,
    ( spl6_100
    | spl6_56
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f642,f71,f61,f337,f663])).

fof(f337,plain,
    ( spl6_56
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f61,plain,
    ( spl6_6
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f642,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X3,sK3)
        | r2_hidden(X3,sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f606,f36])).

fof(f606,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X6,sK0)
        | ~ r2_hidden(X7,sK3) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f62,f330])).

fof(f62,plain,
    ( sK0 = sK2
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f628,plain,
    ( ~ spl6_37
    | spl6_5
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f626,f340,f58,f232])).

fof(f58,plain,
    ( spl6_5
  <=> sK1 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f340,plain,
    ( spl6_58
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f626,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_5
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f613,f341])).

fof(f341,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK3)
        | ~ r2_hidden(X8,sK1) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f340])).

fof(f613,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f34,f59])).

fof(f59,plain,
    ( sK1 != sK3
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f625,plain,
    ( ~ spl6_36
    | spl6_39
    | ~ spl6_58 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl6_36
    | ~ spl6_39
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f622,f230])).

fof(f230,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_36
  <=> r2_hidden(sK5(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f622,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_39
    | ~ spl6_58 ),
    inference(resolution,[],[f341,f239])).

fof(f239,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_39
  <=> ~ r2_hidden(sK5(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f598,plain,
    ( spl6_3
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f590,f52])).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f590,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_94 ),
    inference(resolution,[],[f565,f29])).

fof(f565,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f564])).

fof(f596,plain,
    ( ~ spl6_22
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_94 ),
    inference(resolution,[],[f565,f149])).

fof(f149,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_22
  <=> r2_hidden(sK5(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f595,plain,
    ( ~ spl6_24
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_94 ),
    inference(resolution,[],[f565,f163])).

fof(f163,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK1)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_24
  <=> r2_hidden(sK5(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f589,plain,
    ( spl6_45
    | ~ spl6_46
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl6_45
    | ~ spl6_46
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f583,f273])).

fof(f273,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_46
  <=> r2_hidden(sK5(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f583,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl6_45
    | ~ spl6_96 ),
    inference(resolution,[],[f568,f270])).

fof(f270,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK2)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl6_45
  <=> ~ r2_hidden(sK5(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f587,plain,
    ( ~ spl6_28
    | spl6_31
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_31
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f582,f181])).

fof(f181,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_28
  <=> r2_hidden(sK5(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f582,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_31
    | ~ spl6_96 ),
    inference(resolution,[],[f568,f190])).

fof(f190,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK5(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f576,plain,
    ( ~ spl6_99
    | spl6_53
    | spl6_55 ),
    inference(avatar_split_clause,[],[f500,f316,f310,f574])).

fof(f574,plain,
    ( spl6_99
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f310,plain,
    ( spl6_53
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f316,plain,
    ( spl6_55
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f500,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_53
    | ~ spl6_55 ),
    inference(backward_demodulation,[],[f321,f311])).

fof(f311,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f310])).

fof(f321,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl6_53
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f320,f317])).

fof(f317,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f316])).

fof(f320,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl6_53 ),
    inference(resolution,[],[f311,f33])).

fof(f569,plain,
    ( spl6_94
    | spl6_96
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f348,f71,f567,f564])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f81,f37])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl6_8 ),
    inference(superposition,[],[f35,f72])).

fof(f557,plain,
    ( spl6_65
    | spl6_87
    | spl6_89 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl6_65
    | ~ spl6_87
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f555,f366])).

fof(f366,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl6_65
  <=> k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f555,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl6_87
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f554,f487])).

fof(f487,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl6_87
  <=> ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f554,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl6_89 ),
    inference(resolution,[],[f493,f33])).

fof(f493,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl6_89
  <=> ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f552,plain,
    ( spl6_84
    | spl6_65
    | spl6_83 ),
    inference(avatar_split_clause,[],[f481,f465,f365,f468])).

fof(f468,plain,
    ( spl6_84
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f465,plain,
    ( spl6_83
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f481,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl6_65
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f477,f366])).

fof(f477,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl6_83 ),
    inference(resolution,[],[f466,f33])).

fof(f466,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f465])).

fof(f545,plain,
    ( spl6_92
    | ~ spl6_8
    | spl6_41
    | spl6_43 ),
    inference(avatar_split_clause,[],[f504,f257,f251,f71,f543])).

fof(f504,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_41
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f261,f72])).

fof(f534,plain,
    ( spl6_22
    | spl6_41
    | spl6_43
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f514,f427,f257,f251,f148])).

fof(f427,plain,
    ( spl6_76
  <=> r2_hidden(sK5(k1_xboole_0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f514,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),sK1)
    | ~ spl6_41
    | ~ spl6_43
    | ~ spl6_76 ),
    inference(backward_demodulation,[],[f261,f428])).

fof(f428,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),sK3)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f427])).

fof(f532,plain,
    ( spl6_4
    | spl6_41
    | spl6_43 ),
    inference(avatar_split_clause,[],[f261,f257,f251,f55])).

fof(f530,plain,
    ( ~ spl6_21
    | spl6_41
    | spl6_43
    | spl6_75 ),
    inference(avatar_split_clause,[],[f513,f424,f257,f251,f145])).

fof(f145,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f424,plain,
    ( spl6_75
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f513,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_41
    | ~ spl6_43
    | ~ spl6_75 ),
    inference(backward_demodulation,[],[f261,f425])).

fof(f425,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f424])).

fof(f529,plain,
    ( ~ spl6_91
    | spl6_37
    | spl6_41
    | spl6_43 ),
    inference(avatar_split_clause,[],[f506,f257,f251,f232,f527])).

fof(f527,plain,
    ( spl6_91
  <=> ~ r2_hidden(sK5(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f506,plain,
    ( ~ r2_hidden(sK5(sK1,sK1),sK1)
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f261,f233])).

fof(f499,plain,
    ( spl6_41
    | ~ spl6_42
    | ~ spl6_58 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f495,f255])).

fof(f255,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl6_42
  <=> r2_hidden(sK5(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f495,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl6_41
    | ~ spl6_58 ),
    inference(resolution,[],[f341,f252])).

fof(f494,plain,
    ( ~ spl6_87
    | ~ spl6_89
    | spl6_65 ),
    inference(avatar_split_clause,[],[f458,f365,f492,f486])).

fof(f458,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | ~ spl6_65 ),
    inference(extensionality_resolution,[],[f34,f366])).

fof(f480,plain,
    ( spl6_65
    | spl6_83
    | spl6_85 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl6_65
    | ~ spl6_83
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f478,f366])).

fof(f478,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl6_83
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f477,f472])).

fof(f472,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl6_85
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f475,plain,
    ( spl6_80
    | spl6_63
    | spl6_79 ),
    inference(avatar_split_clause,[],[f456,f443,f356,f446])).

fof(f446,plain,
    ( spl6_80
  <=> r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f443,plain,
    ( spl6_79
  <=> ~ r2_hidden(sK5(sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f456,plain,
    ( r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl6_63
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f452,f357])).

fof(f452,plain,
    ( r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK3
    | ~ spl6_79 ),
    inference(resolution,[],[f444,f33])).

fof(f444,plain,
    ( ~ r2_hidden(sK5(sK3,k1_xboole_0),sK3)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f443])).

fof(f473,plain,
    ( ~ spl6_83
    | ~ spl6_85
    | spl6_65 ),
    inference(avatar_split_clause,[],[f457,f365,f471,f465])).

fof(f457,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_65 ),
    inference(extensionality_resolution,[],[f34,f366])).

fof(f459,plain,
    ( spl6_72
    | spl6_61
    | spl6_71 ),
    inference(avatar_split_clause,[],[f408,f395,f350,f398])).

fof(f398,plain,
    ( spl6_72
  <=> r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f395,plain,
    ( spl6_71
  <=> ~ r2_hidden(sK5(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f408,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_61
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f404,f351])).

fof(f404,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl6_71 ),
    inference(resolution,[],[f396,f33])).

fof(f396,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0),sK2)
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f395])).

fof(f455,plain,
    ( spl6_63
    | spl6_79
    | spl6_81 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl6_63
    | ~ spl6_79
    | ~ spl6_81 ),
    inference(subsumption_resolution,[],[f453,f357])).

fof(f453,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_79
    | ~ spl6_81 ),
    inference(subsumption_resolution,[],[f452,f450])).

fof(f450,plain,
    ( ~ r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl6_81
  <=> ~ r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f451,plain,
    ( ~ spl6_79
    | ~ spl6_81
    | spl6_63 ),
    inference(avatar_split_clause,[],[f389,f356,f449,f443])).

fof(f389,plain,
    ( ~ r2_hidden(sK5(sK3,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5(sK3,k1_xboole_0),sK3)
    | ~ spl6_63 ),
    inference(extensionality_resolution,[],[f34,f357])).

fof(f437,plain,
    ( spl6_63
    | spl6_75
    | spl6_77 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl6_63
    | ~ spl6_75
    | ~ spl6_77 ),
    inference(subsumption_resolution,[],[f435,f357])).

fof(f435,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_75
    | ~ spl6_77 ),
    inference(subsumption_resolution,[],[f434,f425])).

fof(f434,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | k1_xboole_0 = sK3
    | ~ spl6_77 ),
    inference(resolution,[],[f431,f33])).

fof(f431,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK3),sK3)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl6_77
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f432,plain,
    ( ~ spl6_75
    | ~ spl6_77
    | spl6_63 ),
    inference(avatar_split_clause,[],[f388,f356,f430,f424])).

fof(f388,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK3),sK3)
    | ~ r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl6_63 ),
    inference(extensionality_resolution,[],[f34,f357])).

fof(f419,plain,
    ( spl6_1
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f409,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f409,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_56 ),
    inference(resolution,[],[f338,f29])).

fof(f338,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f337])).

fof(f417,plain,
    ( ~ spl6_16
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl6_16
    | ~ spl6_56 ),
    inference(resolution,[],[f338,f125])).

fof(f125,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0),sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_16
  <=> r2_hidden(sK5(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f416,plain,
    ( ~ spl6_28
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_56 ),
    inference(resolution,[],[f338,f181])).

fof(f415,plain,
    ( ~ spl6_46
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl6_46
    | ~ spl6_56 ),
    inference(resolution,[],[f338,f273])).

fof(f407,plain,
    ( spl6_61
    | spl6_71
    | spl6_73 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl6_61
    | ~ spl6_71
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f405,f351])).

fof(f405,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_71
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f404,f402])).

fof(f402,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl6_73
  <=> ~ r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f403,plain,
    ( ~ spl6_71
    | ~ spl6_73
    | spl6_61 ),
    inference(avatar_split_clause,[],[f369,f350,f401,f395])).

fof(f369,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5(sK2,k1_xboole_0),sK2)
    | ~ spl6_61 ),
    inference(extensionality_resolution,[],[f34,f351])).

fof(f387,plain,
    ( spl6_61
    | spl6_67
    | spl6_69 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl6_61
    | ~ spl6_67
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f385,f351])).

fof(f385,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_67
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f384,f375])).

fof(f375,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_67
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f384,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl6_69 ),
    inference(resolution,[],[f381,f33])).

fof(f382,plain,
    ( ~ spl6_67
    | ~ spl6_69
    | spl6_61 ),
    inference(avatar_split_clause,[],[f368,f350,f380,f374])).

fof(f368,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK2),sK2)
    | ~ r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl6_61 ),
    inference(extensionality_resolution,[],[f34,f351])).

fof(f367,plain,
    ( spl6_60
    | spl6_62
    | ~ spl6_65
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f87,f71,f365,f359,f353])).

fof(f353,plain,
    ( spl6_60
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f359,plain,
    ( spl6_62
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f87,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(superposition,[],[f26,f72])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',t113_zfmisc_1)).

fof(f342,plain,
    ( spl6_56
    | spl6_58
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f327,f71,f340,f337])).

fof(f327,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(X8,sK1)
        | ~ r2_hidden(X9,sK0)
        | r2_hidden(X8,sK3) )
    | ~ spl6_8 ),
    inference(resolution,[],[f37,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,sK3) )
    | ~ spl6_8 ),
    inference(superposition,[],[f36,f72])).

fof(f323,plain,
    ( spl6_35
    | spl6_53
    | spl6_55 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl6_35
    | ~ spl6_53
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f321,f214])).

fof(f214,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl6_35
  <=> k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f319,plain,
    ( spl6_6
    | spl6_28
    | spl6_31 ),
    inference(avatar_split_clause,[],[f193,f189,f180,f61])).

fof(f193,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | sK0 = sK2
    | ~ spl6_31 ),
    inference(resolution,[],[f190,f33])).

fof(f318,plain,
    ( ~ spl6_53
    | ~ spl6_55
    | spl6_35 ),
    inference(avatar_split_clause,[],[f227,f213,f316,f310])).

fof(f227,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_35 ),
    inference(extensionality_resolution,[],[f34,f214])).

fof(f303,plain,
    ( spl6_46
    | spl6_7
    | spl6_45 ),
    inference(avatar_split_clause,[],[f282,f269,f64,f272])).

fof(f64,plain,
    ( spl6_7
  <=> sK0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f282,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl6_7
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f278,f65])).

fof(f65,plain,
    ( sK0 != sK2
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f278,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | sK0 = sK2
    | ~ spl6_45 ),
    inference(resolution,[],[f270,f33])).

fof(f302,plain,
    ( spl6_35
    | spl6_49
    | spl6_51 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl6_35
    | ~ spl6_49
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f300,f214])).

fof(f300,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl6_49
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f299,f288])).

fof(f288,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl6_49
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f299,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl6_51 ),
    inference(resolution,[],[f294,f33])).

fof(f294,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl6_51
  <=> ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f296,plain,
    ( spl6_42
    | spl6_5
    | spl6_41 ),
    inference(avatar_split_clause,[],[f264,f251,f58,f254])).

fof(f264,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl6_5
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f295,plain,
    ( ~ spl6_49
    | ~ spl6_51
    | spl6_35 ),
    inference(avatar_split_clause,[],[f226,f213,f293,f287])).

fof(f226,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_35 ),
    inference(extensionality_resolution,[],[f34,f214])).

fof(f281,plain,
    ( spl6_7
    | spl6_45
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_45
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f279,f65])).

fof(f279,plain,
    ( sK0 = sK2
    | ~ spl6_45
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f278,f276])).

fof(f277,plain,
    ( ~ spl6_45
    | ~ spl6_47
    | spl6_7 ),
    inference(avatar_split_clause,[],[f220,f64,f275,f269])).

fof(f220,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK0)
    | ~ r2_hidden(sK5(sK2,sK0),sK2)
    | ~ spl6_7 ),
    inference(extensionality_resolution,[],[f34,f65])).

fof(f263,plain,
    ( spl6_5
    | spl6_41
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_41
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f261,f59])).

fof(f259,plain,
    ( ~ spl6_41
    | ~ spl6_43
    | spl6_5 ),
    inference(avatar_split_clause,[],[f100,f58,f257,f251])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK1)
    | ~ r2_hidden(sK5(sK3,sK1),sK3)
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f34,f59])).

fof(f245,plain,
    ( spl6_5
    | spl6_37
    | spl6_39 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_37
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f243,f59])).

fof(f243,plain,
    ( sK1 = sK3
    | ~ spl6_37
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f242,f233])).

fof(f242,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | sK1 = sK3
    | ~ spl6_39 ),
    inference(resolution,[],[f239,f33])).

fof(f240,plain,
    ( ~ spl6_37
    | ~ spl6_39
    | spl6_5 ),
    inference(avatar_split_clause,[],[f99,f58,f238,f232])).

fof(f99,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK5(sK1,sK3),sK1)
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f34,f59])).

fof(f225,plain,
    ( spl6_20
    | spl6_3
    | spl6_23 ),
    inference(avatar_split_clause,[],[f159,f151,f51,f142])).

fof(f142,plain,
    ( spl6_20
  <=> r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f151,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f159,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f155,f52])).

fof(f155,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl6_23 ),
    inference(resolution,[],[f152,f33])).

fof(f152,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK1),sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f218,plain,
    ( spl6_34
    | ~ spl6_8
    | spl6_29
    | spl6_31 ),
    inference(avatar_split_clause,[],[f197,f189,f183,f71,f216])).

fof(f216,plain,
    ( spl6_34
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f197,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl6_8
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f194,f72])).

fof(f194,plain,
    ( sK0 = sK2
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f193,f184])).

fof(f209,plain,
    ( ~ spl6_33
    | spl6_29
    | spl6_31 ),
    inference(avatar_split_clause,[],[f200,f189,f183,f207])).

fof(f207,plain,
    ( spl6_33
  <=> ~ r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f200,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f194,f184])).

fof(f196,plain,
    ( spl6_7
    | spl6_29
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f194,f65])).

fof(f191,plain,
    ( ~ spl6_29
    | ~ spl6_31
    | spl6_7 ),
    inference(avatar_split_clause,[],[f97,f64,f189,f183])).

fof(f97,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | ~ r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_7 ),
    inference(extensionality_resolution,[],[f34,f65])).

fof(f177,plain,
    ( spl6_3
    | spl6_25
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f175,f52])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f174,f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK5(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK5(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f174,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl6_25 ),
    inference(resolution,[],[f166,f33])).

fof(f166,plain,
    ( ~ r2_hidden(sK5(sK1,k1_xboole_0),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_25
  <=> ~ r2_hidden(sK5(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f173,plain,
    ( ~ spl6_25
    | ~ spl6_27
    | spl6_3 ),
    inference(avatar_split_clause,[],[f96,f51,f171,f165])).

fof(f96,plain,
    ( ~ r2_hidden(sK5(sK1,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5(sK1,k1_xboole_0),sK1)
    | ~ spl6_3 ),
    inference(extensionality_resolution,[],[f34,f52])).

fof(f160,plain,
    ( spl6_12
    | spl6_1
    | spl6_15 ),
    inference(avatar_split_clause,[],[f122,f114,f44,f105])).

fof(f105,plain,
    ( spl6_12
  <=> r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f114,plain,
    ( spl6_15
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f122,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f118,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl6_15 ),
    inference(resolution,[],[f115,f33])).

fof(f115,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK0),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f158,plain,
    ( spl6_3
    | spl6_21
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f156,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f155,f146])).

fof(f146,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f153,plain,
    ( ~ spl6_21
    | ~ spl6_23
    | spl6_3 ),
    inference(avatar_split_clause,[],[f95,f51,f151,f145])).

fof(f95,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK1),sK1)
    | ~ r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_3 ),
    inference(extensionality_resolution,[],[f34,f52])).

fof(f139,plain,
    ( spl6_1
    | spl6_17
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f136,f134])).

fof(f134,plain,
    ( ~ r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f136,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl6_17 ),
    inference(resolution,[],[f128,f33])).

fof(f128,plain,
    ( ~ r2_hidden(sK5(sK0,k1_xboole_0),sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK5(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f135,plain,
    ( ~ spl6_17
    | ~ spl6_19
    | spl6_1 ),
    inference(avatar_split_clause,[],[f94,f44,f133,f127])).

fof(f94,plain,
    ( ~ r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5(sK0,k1_xboole_0),sK0)
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f34,f45])).

fof(f121,plain,
    ( spl6_1
    | spl6_13
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f118,f109])).

fof(f109,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f116,plain,
    ( ~ spl6_13
    | ~ spl6_15
    | spl6_1 ),
    inference(avatar_split_clause,[],[f93,f44,f114,f108])).

fof(f93,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK0),sK0)
    | ~ r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f34,f45])).

fof(f80,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f78,plain,
    ( spl6_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',d2_xboole_0)).

fof(f73,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f23,f71])).

fof(f23,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t134_zfmisc_1.p',t134_zfmisc_1)).

fof(f66,plain,
    ( ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f22,f64,f58])).

fof(f22,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
