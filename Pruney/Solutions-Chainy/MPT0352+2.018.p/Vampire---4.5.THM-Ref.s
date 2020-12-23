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
% DateTime   : Thu Dec  3 12:44:16 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  548 (1691 expanded)
%              Number of leaves         :  135 ( 669 expanded)
%              Depth                    :   14
%              Number of atoms          : 1242 (4935 expanded)
%              Number of equality atoms :  132 ( 728 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f87,f92,f98,f108,f124,f129,f148,f156,f161,f181,f193,f198,f206,f222,f231,f238,f247,f260,f272,f277,f299,f308,f309,f316,f325,f347,f352,f389,f394,f413,f417,f420,f434,f446,f464,f468,f470,f472,f493,f512,f519,f528,f562,f567,f577,f610,f617,f642,f647,f668,f673,f682,f687,f697,f731,f752,f760,f769,f776,f1004,f1033,f1038,f1043,f1054,f1064,f1092,f1097,f1102,f1125,f1151,f1157,f1181,f1186,f1274,f1325,f1405,f1454,f1473,f1580,f1585,f1666,f1697,f1773,f1784,f1849,f1899,f1920,f1941,f1972,f2007,f2080,f2085,f2734,f2952,f2977,f3123,f3128,f3133,f3197,f3202,f3272,f3277,f3282,f3498,f3550,f5024,f5288,f5737,f5853,f5858,f5863,f5974,f6024,f6068,f6088,f6282,f6287,f6354,f6417,f6422,f6496,f6564])).

fof(f6564,plain,
    ( ~ spl4_5
    | spl4_107 ),
    inference(avatar_contradiction_clause,[],[f6563])).

fof(f6563,plain,
    ( $false
    | ~ spl4_5
    | spl4_107 ),
    inference(subsumption_resolution,[],[f6562,f3933])).

fof(f3933,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK0))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f97,f3761,f216])).

fof(f216,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X7)
      | k1_xboole_0 = k4_xboole_0(X9,X8) ) ),
    inference(resolution,[],[f66,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3761,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f796,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f796,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f113,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f113,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f44,f61])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f97,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f6562,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | spl4_107 ),
    inference(forward_demodulation,[],[f6510,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f6510,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2)))
    | spl4_107 ),
    inference(unit_resulting_resolution,[],[f5973,f536])).

fof(f536,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14))
      | r1_tarski(k4_xboole_0(X12,X13),X14) ) ),
    inference(superposition,[],[f60,f62])).

fof(f5973,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))
    | spl4_107 ),
    inference(avatar_component_clause,[],[f5971])).

fof(f5971,plain,
    ( spl4_107
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f6496,plain,
    ( ~ spl4_116
    | spl4_114 ),
    inference(avatar_split_clause,[],[f6424,f6414,f6493])).

fof(f6493,plain,
    ( spl4_116
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f6414,plain,
    ( spl4_114
  <=> r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f6424,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_114 ),
    inference(unit_resulting_resolution,[],[f43,f6416,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f6416,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_114 ),
    inference(avatar_component_clause,[],[f6414])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f6422,plain,
    ( ~ spl4_115
    | spl4_113 ),
    inference(avatar_split_clause,[],[f6410,f6351,f6419])).

fof(f6419,plain,
    ( spl4_115
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f6351,plain,
    ( spl4_113
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f6410,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_113 ),
    inference(unit_resulting_resolution,[],[f43,f6353,f47])).

fof(f6353,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_113 ),
    inference(avatar_component_clause,[],[f6351])).

fof(f6417,plain,
    ( ~ spl4_114
    | spl4_111 ),
    inference(avatar_split_clause,[],[f6298,f6279,f6414])).

fof(f6279,plain,
    ( spl4_111
  <=> r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).

fof(f6298,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_111 ),
    inference(unit_resulting_resolution,[],[f6281,f68])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f6281,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | spl4_111 ),
    inference(avatar_component_clause,[],[f6279])).

fof(f6354,plain,
    ( ~ spl4_113
    | spl4_106 ),
    inference(avatar_split_clause,[],[f6209,f5860,f6351])).

fof(f5860,plain,
    ( spl4_106
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f6209,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))
    | spl4_106 ),
    inference(unit_resulting_resolution,[],[f5862,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f61,f68])).

fof(f5862,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2))
    | spl4_106 ),
    inference(avatar_component_clause,[],[f5860])).

fof(f6287,plain,
    ( ~ spl4_112
    | spl4_106 ),
    inference(avatar_split_clause,[],[f6210,f5860,f6284])).

fof(f6284,plain,
    ( spl4_112
  <=> r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f6210,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2))
    | spl4_106 ),
    inference(unit_resulting_resolution,[],[f5862,f61])).

fof(f6282,plain,
    ( ~ spl4_111
    | ~ spl4_5
    | spl4_106 ),
    inference(avatar_split_clause,[],[f6197,f5860,f95,f6279])).

fof(f6197,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_5
    | spl4_106 ),
    inference(unit_resulting_resolution,[],[f97,f5862,f216])).

fof(f6088,plain,
    ( ~ spl4_110
    | spl4_109 ),
    inference(avatar_split_clause,[],[f6081,f6065,f6085])).

fof(f6085,plain,
    ( spl4_110
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f6065,plain,
    ( spl4_109
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f6081,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))
    | spl4_109 ),
    inference(unit_resulting_resolution,[],[f43,f6067,f47])).

fof(f6067,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))
    | spl4_109 ),
    inference(avatar_component_clause,[],[f6065])).

fof(f6068,plain,
    ( ~ spl4_109
    | spl4_42
    | ~ spl4_103 ),
    inference(avatar_split_clause,[],[f6015,f5734,f607,f6065])).

fof(f607,plain,
    ( spl4_42
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f5734,plain,
    ( spl4_103
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f6015,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))
    | spl4_42
    | ~ spl4_103 ),
    inference(subsumption_resolution,[],[f5995,f609])).

fof(f609,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f607])).

fof(f5995,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_103 ),
    inference(superposition,[],[f111,f5736])).

fof(f5736,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_103 ),
    inference(avatar_component_clause,[],[f5734])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k4_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f68])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f6024,plain,
    ( ~ spl4_108
    | spl4_42
    | ~ spl4_103 ),
    inference(avatar_split_clause,[],[f6014,f5734,f607,f6021])).

fof(f6021,plain,
    ( spl4_108
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f6014,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl4_42
    | ~ spl4_103 ),
    inference(subsumption_resolution,[],[f5986,f609])).

fof(f5986,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_103 ),
    inference(superposition,[],[f53,f5736])).

fof(f5974,plain,
    ( ~ spl4_107
    | ~ spl4_32
    | spl4_39 ),
    inference(avatar_split_clause,[],[f3664,f559,f410,f5971])).

fof(f410,plain,
    ( spl4_32
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f559,plain,
    ( spl4_39
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f3664,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))
    | ~ spl4_32
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f412,f2127,f66])).

fof(f2127,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f561,f328,f214])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f66,f53])).

fof(f328,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(unit_resulting_resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f561,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f559])).

fof(f412,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f410])).

fof(f5863,plain,
    ( ~ spl4_106
    | ~ spl4_45
    | spl4_81 ),
    inference(avatar_split_clause,[],[f3110,f1896,f644,f5860])).

fof(f644,plain,
    ( spl4_45
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1896,plain,
    ( spl4_81
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f3110,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_45
    | spl4_81 ),
    inference(forward_demodulation,[],[f3109,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3109,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_45
    | spl4_81 ),
    inference(forward_demodulation,[],[f3089,f1191])).

fof(f1191,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1)
    | ~ spl4_45 ),
    inference(superposition,[],[f46,f954])).

fof(f954,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f904,f61])).

fof(f904,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_45 ),
    inference(backward_demodulation,[],[f651,f899])).

fof(f899,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f839,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f839,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f812,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f812,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f798,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f798,plain,(
    ! [X2,X3] : r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f44,f113])).

fof(f651,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f646,f63])).

fof(f646,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f644])).

fof(f3089,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))
    | spl4_81 ),
    inference(unit_resulting_resolution,[],[f1898,f536])).

fof(f1898,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK2)
    | spl4_81 ),
    inference(avatar_component_clause,[],[f1896])).

fof(f5858,plain,
    ( ~ spl4_105
    | spl4_81 ),
    inference(avatar_split_clause,[],[f1911,f1896,f5855])).

fof(f5855,plain,
    ( spl4_105
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f1911,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | spl4_81 ),
    inference(unit_resulting_resolution,[],[f1898,f60])).

fof(f5853,plain,
    ( spl4_104
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f1250,f1122,f5850])).

fof(f5850,plain,
    ( spl4_104
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1122,plain,
    ( spl4_65
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1250,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl4_65 ),
    inference(superposition,[],[f1124,f62])).

fof(f1124,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f5737,plain,
    ( spl4_103
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f578,f574,f5734])).

fof(f574,plain,
    ( spl4_41
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f578,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f576,f54])).

fof(f576,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f574])).

fof(f5288,plain,
    ( spl4_102
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f570,f564,f5285])).

fof(f5285,plain,
    ( spl4_102
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f564,plain,
    ( spl4_40
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f570,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f566,f54])).

fof(f566,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f564])).

fof(f5024,plain,
    ( spl4_101
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f1049,f1001,f5021])).

fof(f5021,plain,
    ( spl4_101
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f1001,plain,
    ( spl4_56
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f1049,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f43,f1003,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1003,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f3550,plain,
    ( ~ spl4_100
    | spl4_99 ),
    inference(avatar_split_clause,[],[f3515,f3495,f3547])).

fof(f3547,plain,
    ( spl4_100
  <=> m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f3495,plain,
    ( spl4_99
  <=> r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f3515,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2)))
    | spl4_99 ),
    inference(unit_resulting_resolution,[],[f43,f3497,f47])).

fof(f3497,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2)))
    | spl4_99 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f3498,plain,
    ( ~ spl4_99
    | spl4_70 ),
    inference(avatar_split_clause,[],[f1301,f1271,f3495])).

fof(f1271,plain,
    ( spl4_70
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1301,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2)))
    | spl4_70 ),
    inference(unit_resulting_resolution,[],[f1273,f68])).

fof(f1273,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_70 ),
    inference(avatar_component_clause,[],[f1271])).

fof(f3282,plain,
    ( ~ spl4_98
    | spl4_93 ),
    inference(avatar_split_clause,[],[f3228,f3130,f3279])).

fof(f3279,plain,
    ( spl4_98
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f3130,plain,
    ( spl4_93
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f3228,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2))
    | spl4_93 ),
    inference(unit_resulting_resolution,[],[f43,f3132,f47])).

fof(f3132,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2))
    | spl4_93 ),
    inference(avatar_component_clause,[],[f3130])).

fof(f3277,plain,
    ( ~ spl4_97
    | spl4_92 ),
    inference(avatar_split_clause,[],[f3208,f3125,f3274])).

fof(f3274,plain,
    ( spl4_97
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f3125,plain,
    ( spl4_92
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f3208,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_92 ),
    inference(unit_resulting_resolution,[],[f43,f3127,f47])).

fof(f3127,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_92 ),
    inference(avatar_component_clause,[],[f3125])).

fof(f3272,plain,
    ( ~ spl4_96
    | spl4_91 ),
    inference(avatar_split_clause,[],[f3204,f3120,f3269])).

fof(f3269,plain,
    ( spl4_96
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f3120,plain,
    ( spl4_91
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f3204,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_91 ),
    inference(unit_resulting_resolution,[],[f43,f3122,f47])).

fof(f3122,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f3120])).

fof(f3202,plain,
    ( ~ spl4_95
    | spl4_90 ),
    inference(avatar_split_clause,[],[f3041,f2974,f3199])).

fof(f3199,plain,
    ( spl4_95
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f2974,plain,
    ( spl4_90
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f3041,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2))
    | spl4_90 ),
    inference(unit_resulting_resolution,[],[f43,f2976,f47])).

fof(f2976,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2))
    | spl4_90 ),
    inference(avatar_component_clause,[],[f2974])).

fof(f3197,plain,
    ( ~ spl4_94
    | spl4_89 ),
    inference(avatar_split_clause,[],[f3037,f2949,f3194])).

fof(f3194,plain,
    ( spl4_94
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f2949,plain,
    ( spl4_89
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f3037,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_89 ),
    inference(unit_resulting_resolution,[],[f43,f2951,f47])).

fof(f2951,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_89 ),
    inference(avatar_component_clause,[],[f2949])).

fof(f3133,plain,
    ( ~ spl4_93
    | spl4_84 ),
    inference(avatar_split_clause,[],[f1999,f1969,f3130])).

fof(f1969,plain,
    ( spl4_84
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1999,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2))
    | spl4_84 ),
    inference(unit_resulting_resolution,[],[f1971,f68])).

fof(f1971,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | spl4_84 ),
    inference(avatar_component_clause,[],[f1969])).

fof(f3128,plain,
    ( ~ spl4_92
    | spl4_83 ),
    inference(avatar_split_clause,[],[f1984,f1938,f3125])).

fof(f1938,plain,
    ( spl4_83
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f1984,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_83 ),
    inference(unit_resulting_resolution,[],[f1940,f68])).

fof(f1940,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl4_83 ),
    inference(avatar_component_clause,[],[f1938])).

fof(f3123,plain,
    ( ~ spl4_91
    | spl4_74 ),
    inference(avatar_split_clause,[],[f1482,f1470,f3120])).

fof(f1470,plain,
    ( spl4_74
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1482,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_74 ),
    inference(unit_resulting_resolution,[],[f1472,f68])).

fof(f1472,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f2977,plain,
    ( ~ spl4_90
    | spl4_82 ),
    inference(avatar_split_clause,[],[f1933,f1917,f2974])).

fof(f1917,plain,
    ( spl4_82
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1933,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2))
    | spl4_82 ),
    inference(unit_resulting_resolution,[],[f1919,f68])).

fof(f1919,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK2)
    | spl4_82 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f2952,plain,
    ( ~ spl4_89
    | spl4_73 ),
    inference(avatar_split_clause,[],[f1464,f1451,f2949])).

fof(f1451,plain,
    ( spl4_73
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1464,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_73 ),
    inference(unit_resulting_resolution,[],[f1453,f68])).

fof(f1453,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | spl4_73 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f2734,plain,
    ( ~ spl4_88
    | spl4_86 ),
    inference(avatar_split_clause,[],[f2254,f2077,f2731])).

fof(f2731,plain,
    ( spl4_88
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f2077,plain,
    ( spl4_86
  <=> r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f2254,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_86 ),
    inference(unit_resulting_resolution,[],[f43,f2079,f47])).

fof(f2079,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_86 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2085,plain,
    ( ~ spl4_87
    | spl4_85 ),
    inference(avatar_split_clause,[],[f2009,f2004,f2082])).

fof(f2082,plain,
    ( spl4_87
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f2004,plain,
    ( spl4_85
  <=> r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f2009,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | spl4_85 ),
    inference(unit_resulting_resolution,[],[f43,f2006,f47])).

fof(f2006,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f2004])).

fof(f2080,plain,
    ( ~ spl4_86
    | spl4_72 ),
    inference(avatar_split_clause,[],[f1445,f1402,f2077])).

fof(f1402,plain,
    ( spl4_72
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1445,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_72 ),
    inference(unit_resulting_resolution,[],[f1404,f68])).

fof(f1404,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | spl4_72 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f2007,plain,
    ( ~ spl4_85
    | spl4_81 ),
    inference(avatar_split_clause,[],[f1912,f1896,f2004])).

fof(f1912,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | spl4_81 ),
    inference(unit_resulting_resolution,[],[f1898,f68])).

fof(f1972,plain,
    ( ~ spl4_84
    | ~ spl4_32
    | spl4_82 ),
    inference(avatar_split_clause,[],[f1928,f1917,f410,f1969])).

fof(f1928,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl4_32
    | spl4_82 ),
    inference(unit_resulting_resolution,[],[f412,f1919,f66])).

fof(f1941,plain,
    ( ~ spl4_83
    | spl4_51 ),
    inference(avatar_split_clause,[],[f1867,f728,f1938])).

fof(f728,plain,
    ( spl4_51
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1867,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f730,f335])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f63,f53])).

fof(f730,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f728])).

fof(f1920,plain,
    ( ~ spl4_82
    | spl4_42 ),
    inference(avatar_split_clause,[],[f1866,f607,f1917])).

fof(f1866,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK2)
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f609,f335])).

fof(f1899,plain,
    ( ~ spl4_81
    | spl4_39 ),
    inference(avatar_split_clause,[],[f1865,f559,f1896])).

fof(f1865,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK2)
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f561,f335])).

fof(f1849,plain,
    ( ~ spl4_80
    | spl4_79 ),
    inference(avatar_split_clause,[],[f1819,f1781,f1846])).

fof(f1846,plain,
    ( spl4_80
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1781,plain,
    ( spl4_79
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f1819,plain,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | spl4_79 ),
    inference(unit_resulting_resolution,[],[f1783,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1783,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_79 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1784,plain,
    ( ~ spl4_79
    | spl4_78 ),
    inference(avatar_split_clause,[],[f1776,f1770,f1781])).

fof(f1770,plain,
    ( spl4_78
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f1776,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_78 ),
    inference(unit_resulting_resolution,[],[f1771,f51])).

fof(f1771,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl4_78 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f1773,plain,
    ( spl4_78
    | ~ spl4_66
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f171,f126,f1148,f1770])).

fof(f1148,plain,
    ( spl4_66
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f126,plain,
    ( spl4_8
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f171,plain,
    ( k1_xboole_0 != sK2
    | r1_xboole_0(sK2,sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f55,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1697,plain,
    ( ~ spl4_77
    | spl4_76 ),
    inference(avatar_split_clause,[],[f1668,f1663,f1694])).

fof(f1694,plain,
    ( spl4_77
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f1663,plain,
    ( spl4_76
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1668,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl4_76 ),
    inference(unit_resulting_resolution,[],[f1665,f55])).

fof(f1665,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_76 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f1666,plain,
    ( ~ spl4_76
    | spl4_75 ),
    inference(avatar_split_clause,[],[f1658,f1582,f1663])).

fof(f1582,plain,
    ( spl4_75
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1658,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_75 ),
    inference(unit_resulting_resolution,[],[f1583,f51])).

fof(f1583,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl4_75 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1585,plain,
    ( spl4_75
    | ~ spl4_60
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f138,f121,f1051,f1582])).

fof(f1051,plain,
    ( spl4_60
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f121,plain,
    ( spl4_7
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f138,plain,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(sK1,sK0)
    | ~ spl4_7 ),
    inference(superposition,[],[f55,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1580,plain,
    ( spl4_61
    | ~ spl4_23
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f137,f121,f274,f1061])).

fof(f1061,plain,
    ( spl4_61
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f274,plain,
    ( spl4_23
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f137,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(superposition,[],[f53,f123])).

fof(f1473,plain,
    ( ~ spl4_74
    | spl4_51 ),
    inference(avatar_split_clause,[],[f1381,f728,f1470])).

fof(f1381,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f730,f800])).

fof(f800,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f53,f113])).

fof(f1454,plain,
    ( ~ spl4_73
    | spl4_42 ),
    inference(avatar_split_clause,[],[f1380,f607,f1451])).

fof(f1380,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f609,f800])).

fof(f1405,plain,
    ( ~ spl4_72
    | spl4_39 ),
    inference(avatar_split_clause,[],[f1379,f559,f1402])).

fof(f1379,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f561,f800])).

fof(f1325,plain,
    ( ~ spl4_71
    | ~ spl4_5
    | ~ spl4_32
    | ~ spl4_46
    | spl4_58 ),
    inference(avatar_split_clause,[],[f1232,f1035,f665,f410,f95,f1322])).

fof(f1322,plain,
    ( spl4_71
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f665,plain,
    ( spl4_46
  <=> r1_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1035,plain,
    ( spl4_58
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1232,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_32
    | ~ spl4_46
    | spl4_58 ),
    inference(unit_resulting_resolution,[],[f412,f1103,f66])).

fof(f1103,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(X0,sK1))
    | ~ spl4_5
    | ~ spl4_46
    | spl4_58 ),
    inference(unit_resulting_resolution,[],[f97,f1047,f66])).

fof(f1047,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK1))
    | ~ spl4_46
    | spl4_58 ),
    inference(forward_demodulation,[],[f1044,f674])).

fof(f674,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f667,f54])).

fof(f667,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f665])).

fof(f1044,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(sK1,k1_xboole_0)))
    | spl4_58 ),
    inference(unit_resulting_resolution,[],[f1037,f53])).

fof(f1037,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1274,plain,
    ( ~ spl4_70
    | ~ spl4_32
    | ~ spl4_46
    | spl4_58 ),
    inference(avatar_split_clause,[],[f1106,f1035,f665,f410,f1271])).

fof(f1106,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_32
    | ~ spl4_46
    | spl4_58 ),
    inference(unit_resulting_resolution,[],[f412,f1047,f66])).

fof(f1186,plain,
    ( spl4_69
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f908,f235,f1183])).

fof(f1183,plain,
    ( spl4_69
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f235,plain,
    ( spl4_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f908,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f365,f899])).

fof(f365,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f237,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f237,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f1181,plain,
    ( spl4_68
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f761,f757,f1178])).

fof(f1178,plain,
    ( spl4_68
  <=> sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f757,plain,
    ( spl4_53
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f761,plain,
    ( sK2 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_53 ),
    inference(unit_resulting_resolution,[],[f759,f54])).

fof(f759,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f757])).

fof(f1157,plain,
    ( spl4_67
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f674,f665,f1154])).

fof(f1154,plain,
    ( spl4_67
  <=> sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1151,plain,
    ( ~ spl4_66
    | spl4_62 ),
    inference(avatar_split_clause,[],[f1145,f1089,f1148])).

fof(f1089,plain,
    ( spl4_62
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1145,plain,
    ( k1_xboole_0 != sK2
    | spl4_62 ),
    inference(superposition,[],[f1091,f899])).

fof(f1091,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)
    | spl4_62 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1125,plain,
    ( spl4_65
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f503,f410,f1122])).

fof(f503,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f412,f61])).

fof(f1102,plain,
    ( spl4_64
    | ~ spl4_45
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f692,f684,f644,f1099])).

fof(f1099,plain,
    ( spl4_64
  <=> k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f684,plain,
    ( spl4_49
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f692,plain,
    ( k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_45
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f690,f661])).

fof(f661,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f646,f61])).

fof(f690,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_49 ),
    inference(unit_resulting_resolution,[],[f686,f52])).

fof(f686,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f684])).

fof(f1097,plain,
    ( spl4_63
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f661,f644,f1094])).

fof(f1094,plain,
    ( spl4_63
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f1092,plain,
    ( ~ spl4_62
    | spl4_34 ),
    inference(avatar_split_clause,[],[f450,f443,f1089])).

fof(f443,plain,
    ( spl4_34
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f450,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f445,f60])).

fof(f445,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f443])).

fof(f1064,plain,
    ( ~ spl4_61
    | spl4_59 ),
    inference(avatar_split_clause,[],[f1058,f1040,f1061])).

fof(f1040,plain,
    ( spl4_59
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f1058,plain,
    ( k1_xboole_0 != sK0
    | spl4_59 ),
    inference(superposition,[],[f1042,f899])).

fof(f1042,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl4_59 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1054,plain,
    ( ~ spl4_60
    | spl4_58 ),
    inference(avatar_split_clause,[],[f1046,f1035,f1051])).

fof(f1046,plain,
    ( k1_xboole_0 != sK1
    | spl4_58 ),
    inference(superposition,[],[f1037,f899])).

fof(f1043,plain,
    ( ~ spl4_59
    | spl4_23 ),
    inference(avatar_split_clause,[],[f291,f274,f1040])).

fof(f291,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f276,f60])).

fof(f276,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1038,plain,
    ( ~ spl4_58
    | spl4_22 ),
    inference(avatar_split_clause,[],[f285,f269,f1035])).

fof(f269,plain,
    ( spl4_22
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f285,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f271,f60])).

fof(f271,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1033,plain,
    ( spl4_57
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f224,f219,f1030])).

fof(f1030,plain,
    ( spl4_57
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f219,plain,
    ( spl4_16
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f224,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f221,f61])).

fof(f221,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f219])).

fof(f1004,plain,
    ( spl4_56
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f504,f410,f1001])).

fof(f504,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f412,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f776,plain,
    ( spl4_55
    | ~ spl4_14
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f764,f757,f195,f773])).

fof(f773,plain,
    ( spl4_55
  <=> sK2 = k3_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f195,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f764,plain,
    ( sK2 = k3_subset_1(sK2,k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_53 ),
    inference(backward_demodulation,[],[f367,f761])).

fof(f367,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k3_subset_1(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f197,f52])).

fof(f197,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f769,plain,
    ( spl4_54
    | ~ spl4_11
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f677,f665,f158,f766])).

fof(f766,plain,
    ( spl4_54
  <=> sK1 = k3_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f158,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f677,plain,
    ( sK1 = k3_subset_1(sK1,k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f366,f674])).

fof(f366,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0)
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f160,f52])).

fof(f160,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f760,plain,
    ( spl4_53
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f754,f749,f757])).

fof(f749,plain,
    ( spl4_52
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f754,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f751,f51])).

fof(f751,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f749])).

fof(f752,plain,
    ( spl4_52
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f733,f614,f749])).

fof(f614,plain,
    ( spl4_43
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f733,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_43 ),
    inference(unit_resulting_resolution,[],[f616,f55])).

fof(f616,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f614])).

fof(f731,plain,
    ( ~ spl4_51
    | spl4_33 ),
    inference(avatar_split_clause,[],[f438,f431,f728])).

fof(f431,plain,
    ( spl4_33
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f438,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl4_33 ),
    inference(unit_resulting_resolution,[],[f433,f60])).

fof(f433,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f431])).

fof(f697,plain,
    ( spl4_50
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f364,f75,f694])).

fof(f694,plain,
    ( spl4_50
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f75,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f364,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f77,f52])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f687,plain,
    ( spl4_49
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f629,f203,f684])).

fof(f203,plain,
    ( spl4_15
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f629,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_15 ),
    inference(superposition,[],[f100,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f100,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f43,f79,f48])).

fof(f79,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f44,f67])).

fof(f682,plain,
    ( spl4_48
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f628,f203,f679])).

fof(f679,plain,
    ( spl4_48
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f628,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_15 ),
    inference(superposition,[],[f79,f205])).

fof(f673,plain,
    ( spl4_47
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f363,f70,f670])).

fof(f670,plain,
    ( spl4_47
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f70,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f363,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f72,f52])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f668,plain,
    ( spl4_46
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f649,f639,f665])).

fof(f639,plain,
    ( spl4_44
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f649,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f641,f51])).

fof(f641,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f639])).

fof(f647,plain,
    ( spl4_45
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f620,f203,f644])).

fof(f620,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_15 ),
    inference(superposition,[],[f44,f205])).

fof(f642,plain,
    ( spl4_44
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f619,f203,f639])).

fof(f619,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f205,f55])).

fof(f617,plain,
    ( spl4_43
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f182,f178,f614])).

fof(f178,plain,
    ( spl4_12
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f182,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f180,f61])).

fof(f180,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f610,plain,
    ( ~ spl4_42
    | spl4_21 ),
    inference(avatar_split_clause,[],[f264,f257,f607])).

fof(f257,plain,
    ( spl4_21
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f264,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f259,f60])).

fof(f259,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f257])).

fof(f577,plain,
    ( spl4_41
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f571,f564,f574])).

fof(f571,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f566,f51])).

fof(f567,plain,
    ( spl4_40
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f498,f410,f564])).

fof(f498,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f412,f65])).

fof(f562,plain,
    ( ~ spl4_39
    | spl4_19 ),
    inference(avatar_split_clause,[],[f479,f240,f559])).

fof(f240,plain,
    ( spl4_19
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f479,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f241,f60])).

fof(f241,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f528,plain,
    ( ~ spl4_38
    | spl4_37 ),
    inference(avatar_split_clause,[],[f521,f516,f525])).

fof(f525,plain,
    ( spl4_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f516,plain,
    ( spl4_37
  <=> r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f521,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_37 ),
    inference(unit_resulting_resolution,[],[f43,f518,f47])).

fof(f518,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f516])).

fof(f519,plain,
    ( ~ spl4_37
    | spl4_34 ),
    inference(avatar_split_clause,[],[f451,f443,f516])).

fof(f451,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f445,f68])).

fof(f512,plain,
    ( ~ spl4_36
    | spl4_35 ),
    inference(avatar_split_clause,[],[f495,f490,f509])).

fof(f509,plain,
    ( spl4_36
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f490,plain,
    ( spl4_35
  <=> r2_hidden(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f495,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | spl4_35 ),
    inference(unit_resulting_resolution,[],[f43,f492,f47])).

fof(f492,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f490])).

fof(f493,plain,
    ( ~ spl4_35
    | spl4_33 ),
    inference(avatar_split_clause,[],[f439,f431,f490])).

fof(f439,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | spl4_33 ),
    inference(unit_resulting_resolution,[],[f433,f68])).

fof(f472,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_19
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_19
    | spl4_20 ),
    inference(subsumption_resolution,[],[f415,f421])).

fof(f421,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f242,f63])).

fof(f242,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f415,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_20 ),
    inference(forward_demodulation,[],[f414,f364])).

fof(f414,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_1
    | spl4_20 ),
    inference(forward_demodulation,[],[f245,f363])).

fof(f245,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_20
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f470,plain,
    ( ~ spl4_19
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl4_19
    | spl4_32 ),
    inference(subsumption_resolution,[],[f461,f242])).

fof(f461,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_32 ),
    inference(resolution,[],[f411,f63])).

fof(f411,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f410])).

fof(f468,plain,
    ( ~ spl4_19
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl4_19
    | spl4_32 ),
    inference(subsumption_resolution,[],[f454,f242])).

fof(f454,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f411,f63])).

fof(f464,plain,
    ( ~ spl4_19
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl4_19
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f242,f411,f63])).

fof(f446,plain,
    ( ~ spl4_34
    | ~ spl4_19
    | spl4_22 ),
    inference(avatar_split_clause,[],[f422,f269,f240,f443])).

fof(f422,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_19
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f271,f242,f66])).

fof(f434,plain,
    ( ~ spl4_33
    | ~ spl4_19
    | spl4_21 ),
    inference(avatar_split_clause,[],[f426,f257,f240,f431])).

fof(f426,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl4_19
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f259,f242,f66])).

fof(f420,plain,
    ( ~ spl4_24
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl4_24
    | spl4_25 ),
    inference(subsumption_resolution,[],[f297,f418])).

fof(f418,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | spl4_25 ),
    inference(subsumption_resolution,[],[f311,f43])).

fof(f311,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl4_25 ),
    inference(resolution,[],[f307,f48])).

fof(f307,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl4_25
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f297,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_24
  <=> r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f417,plain,
    ( ~ spl4_19
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl4_19
    | spl4_24 ),
    inference(subsumption_resolution,[],[f242,f302])).

fof(f302,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_24 ),
    inference(resolution,[],[f298,f67])).

fof(f298,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f413,plain,
    ( spl4_32
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f376,f244,f75,f70,f410])).

fof(f376,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f374,f363])).

fof(f374,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f246,f364])).

fof(f246,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f394,plain,
    ( ~ spl4_31
    | spl4_29 ),
    inference(avatar_split_clause,[],[f358,f349,f391])).

fof(f391,plain,
    ( spl4_31
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f349,plain,
    ( spl4_29
  <=> r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f358,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | spl4_29 ),
    inference(unit_resulting_resolution,[],[f43,f351,f47])).

fof(f351,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f349])).

fof(f389,plain,
    ( ~ spl4_30
    | spl4_28 ),
    inference(avatar_split_clause,[],[f354,f344,f386])).

fof(f386,plain,
    ( spl4_30
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f344,plain,
    ( spl4_28
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f354,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f43,f346,f47])).

fof(f346,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f352,plain,
    ( ~ spl4_29
    | spl4_23 ),
    inference(avatar_split_clause,[],[f292,f274,f349])).

fof(f292,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0))
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f276,f68])).

fof(f347,plain,
    ( ~ spl4_28
    | spl4_22 ),
    inference(avatar_split_clause,[],[f286,f269,f344])).

fof(f286,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f271,f68])).

fof(f325,plain,
    ( ~ spl4_27
    | spl4_26 ),
    inference(avatar_split_clause,[],[f318,f313,f322])).

fof(f322,plain,
    ( spl4_27
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f313,plain,
    ( spl4_26
  <=> r2_hidden(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f318,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f43,f315,f47])).

fof(f315,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f313])).

fof(f316,plain,
    ( ~ spl4_26
    | spl4_21 ),
    inference(avatar_split_clause,[],[f265,f257,f313])).

fof(f265,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK2))
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f259,f68])).

fof(f309,plain,
    ( ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f42,f244,f240])).

fof(f42,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f308,plain,
    ( ~ spl4_25
    | spl4_24 ),
    inference(avatar_split_clause,[],[f301,f296,f305])).

fof(f301,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f43,f298,f47])).

fof(f299,plain,
    ( ~ spl4_24
    | spl4_19 ),
    inference(avatar_split_clause,[],[f253,f240,f296])).

fof(f253,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f241,f68])).

fof(f277,plain,
    ( ~ spl4_23
    | ~ spl4_12
    | spl4_21 ),
    inference(avatar_split_clause,[],[f262,f257,f178,f274])).

fof(f262,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_12
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f180,f259,f66])).

fof(f272,plain,
    ( ~ spl4_22
    | ~ spl4_12
    | spl4_19 ),
    inference(avatar_split_clause,[],[f250,f240,f178,f269])).

fof(f250,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_12
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f180,f241,f66])).

fof(f260,plain,
    ( ~ spl4_21
    | ~ spl4_5
    | spl4_19 ),
    inference(avatar_split_clause,[],[f248,f240,f95,f257])).

fof(f248,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl4_5
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f97,f241,f66])).

fof(f247,plain,
    ( spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f41,f244,f240])).

fof(f41,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f238,plain,
    ( spl4_18
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f233,f228,f235])).

fof(f228,plain,
    ( spl4_17
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f233,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f43,f230,f48])).

fof(f230,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f231,plain,
    ( spl4_17
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f225,f219,f228])).

fof(f225,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f221,f67])).

fof(f222,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f213,f178,f105,f219])).

fof(f105,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f213,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f180,f107,f66])).

fof(f107,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f206,plain,
    ( spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f149,f145,f203])).

fof(f145,plain,
    ( spl4_9
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f149,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f147,f61])).

fof(f147,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f198,plain,
    ( spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f175,f126,f195])).

fof(f175,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_8 ),
    inference(superposition,[],[f100,f128])).

fof(f193,plain,
    ( spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f174,f126,f190])).

fof(f190,plain,
    ( spl4_13
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f174,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_8 ),
    inference(superposition,[],[f79,f128])).

fof(f181,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f169,f126,f178])).

fof(f169,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f44,f128])).

fof(f161,plain,
    ( spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f142,f121,f158])).

fof(f142,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f100,f123])).

fof(f156,plain,
    ( spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f141,f121,f153])).

fof(f153,plain,
    ( spl4_10
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f79,f123])).

fof(f148,plain,
    ( spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f136,f121,f145])).

fof(f136,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_7 ),
    inference(superposition,[],[f44,f123])).

fof(f129,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f105,f126])).

fof(f115,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f107,f61])).

fof(f124,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f114,f95,f121])).

fof(f114,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f97,f61])).

fof(f108,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f102,f89,f105])).

fof(f89,plain,
    ( spl4_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f102,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f91,f68])).

fof(f91,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f98,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f93,f84,f95])).

fof(f84,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f93,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f86,f68])).

fof(f86,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f92,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f82,f75,f89])).

fof(f82,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f43,f77,f47])).

fof(f87,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f81,f70,f84])).

fof(f81,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f43,f72,f47])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (1214349313)
% 0.20/0.37  ipcrm: permission denied for id (1217921026)
% 0.20/0.37  ipcrm: permission denied for id (1217953795)
% 0.20/0.37  ipcrm: permission denied for id (1220804612)
% 0.20/0.37  ipcrm: permission denied for id (1218019333)
% 0.20/0.38  ipcrm: permission denied for id (1214513158)
% 0.20/0.38  ipcrm: permission denied for id (1218052103)
% 0.20/0.38  ipcrm: permission denied for id (1223000072)
% 0.20/0.38  ipcrm: permission denied for id (1220902921)
% 0.20/0.38  ipcrm: permission denied for id (1220935690)
% 0.20/0.38  ipcrm: permission denied for id (1220968459)
% 0.20/0.38  ipcrm: permission denied for id (1218215948)
% 0.20/0.38  ipcrm: permission denied for id (1214709773)
% 0.20/0.39  ipcrm: permission denied for id (1214742542)
% 0.20/0.39  ipcrm: permission denied for id (1218248719)
% 0.20/0.39  ipcrm: permission denied for id (1218281488)
% 0.20/0.39  ipcrm: permission denied for id (1222377489)
% 0.20/0.39  ipcrm: permission denied for id (1218347026)
% 0.20/0.39  ipcrm: permission denied for id (1218379795)
% 0.20/0.39  ipcrm: permission denied for id (1222410260)
% 0.20/0.39  ipcrm: permission denied for id (1218445333)
% 0.20/0.40  ipcrm: permission denied for id (1214939158)
% 0.20/0.40  ipcrm: permission denied for id (1218478103)
% 0.20/0.40  ipcrm: permission denied for id (1218510872)
% 0.20/0.40  ipcrm: permission denied for id (1221066777)
% 0.20/0.40  ipcrm: permission denied for id (1215070234)
% 0.20/0.40  ipcrm: permission denied for id (1218576411)
% 0.20/0.40  ipcrm: permission denied for id (1215103004)
% 0.20/0.40  ipcrm: permission denied for id (1218609181)
% 0.20/0.41  ipcrm: permission denied for id (1221099550)
% 0.20/0.41  ipcrm: permission denied for id (1218674719)
% 0.20/0.41  ipcrm: permission denied for id (1215234080)
% 0.20/0.41  ipcrm: permission denied for id (1218707489)
% 0.20/0.41  ipcrm: permission denied for id (1218740258)
% 0.20/0.41  ipcrm: permission denied for id (1222443043)
% 0.20/0.41  ipcrm: permission denied for id (1221165092)
% 0.20/0.41  ipcrm: permission denied for id (1222475813)
% 0.20/0.42  ipcrm: permission denied for id (1215365158)
% 0.20/0.42  ipcrm: permission denied for id (1218871335)
% 0.20/0.42  ipcrm: permission denied for id (1218904104)
% 0.20/0.42  ipcrm: permission denied for id (1218936873)
% 0.20/0.42  ipcrm: permission denied for id (1218969642)
% 0.20/0.42  ipcrm: permission denied for id (1215463467)
% 0.20/0.42  ipcrm: permission denied for id (1221230636)
% 0.20/0.43  ipcrm: permission denied for id (1221263405)
% 0.20/0.43  ipcrm: permission denied for id (1215561774)
% 0.20/0.43  ipcrm: permission denied for id (1219133488)
% 0.20/0.43  ipcrm: permission denied for id (1221328945)
% 0.20/0.43  ipcrm: permission denied for id (1215692850)
% 0.20/0.43  ipcrm: permission denied for id (1215725619)
% 0.20/0.43  ipcrm: permission denied for id (1223065652)
% 0.20/0.44  ipcrm: permission denied for id (1221427254)
% 0.20/0.44  ipcrm: permission denied for id (1215823927)
% 0.20/0.44  ipcrm: permission denied for id (1215856696)
% 0.20/0.44  ipcrm: permission denied for id (1219297337)
% 0.20/0.44  ipcrm: permission denied for id (1219330106)
% 0.20/0.44  ipcrm: permission denied for id (1215955003)
% 0.20/0.44  ipcrm: permission denied for id (1215987772)
% 0.20/0.45  ipcrm: permission denied for id (1221460029)
% 0.20/0.45  ipcrm: permission denied for id (1216020542)
% 0.20/0.45  ipcrm: permission denied for id (1222606911)
% 0.20/0.45  ipcrm: permission denied for id (1222639680)
% 0.20/0.45  ipcrm: permission denied for id (1216118849)
% 0.20/0.45  ipcrm: permission denied for id (1216151618)
% 0.20/0.45  ipcrm: permission denied for id (1216184387)
% 0.20/0.46  ipcrm: permission denied for id (1221558340)
% 0.20/0.46  ipcrm: permission denied for id (1216249925)
% 0.20/0.46  ipcrm: permission denied for id (1216282694)
% 0.20/0.46  ipcrm: permission denied for id (1216315463)
% 0.20/0.46  ipcrm: permission denied for id (1219526728)
% 0.20/0.46  ipcrm: permission denied for id (1219559497)
% 0.20/0.46  ipcrm: permission denied for id (1222672458)
% 0.20/0.46  ipcrm: permission denied for id (1219625035)
% 0.20/0.47  ipcrm: permission denied for id (1216413772)
% 0.20/0.47  ipcrm: permission denied for id (1216446541)
% 0.20/0.47  ipcrm: permission denied for id (1222705230)
% 0.20/0.47  ipcrm: permission denied for id (1221656655)
% 0.20/0.47  ipcrm: permission denied for id (1221689424)
% 0.20/0.47  ipcrm: permission denied for id (1216577617)
% 0.20/0.47  ipcrm: permission denied for id (1221722194)
% 0.20/0.47  ipcrm: permission denied for id (1216643155)
% 0.20/0.48  ipcrm: permission denied for id (1219788884)
% 0.20/0.48  ipcrm: permission denied for id (1221754965)
% 0.20/0.48  ipcrm: permission denied for id (1221787734)
% 0.20/0.48  ipcrm: permission denied for id (1223131223)
% 0.20/0.48  ipcrm: permission denied for id (1219919960)
% 0.20/0.48  ipcrm: permission denied for id (1219952729)
% 0.20/0.48  ipcrm: permission denied for id (1219985498)
% 0.20/0.48  ipcrm: permission denied for id (1216872539)
% 0.20/0.49  ipcrm: permission denied for id (1221853276)
% 0.20/0.49  ipcrm: permission denied for id (1223163997)
% 0.20/0.49  ipcrm: permission denied for id (1220083806)
% 0.20/0.49  ipcrm: permission denied for id (1216970847)
% 0.20/0.49  ipcrm: permission denied for id (1217003616)
% 0.20/0.49  ipcrm: permission denied for id (1220116577)
% 0.20/0.49  ipcrm: permission denied for id (1220149346)
% 0.20/0.49  ipcrm: permission denied for id (1220182115)
% 0.20/0.50  ipcrm: permission denied for id (1217101924)
% 0.20/0.50  ipcrm: permission denied for id (1221918821)
% 0.20/0.50  ipcrm: permission denied for id (1221951590)
% 0.20/0.50  ipcrm: permission denied for id (1220280423)
% 0.20/0.50  ipcrm: permission denied for id (1222803560)
% 0.20/0.50  ipcrm: permission denied for id (1222017129)
% 0.20/0.50  ipcrm: permission denied for id (1222049898)
% 0.20/0.50  ipcrm: permission denied for id (1217298539)
% 0.20/0.51  ipcrm: permission denied for id (1217331308)
% 0.20/0.51  ipcrm: permission denied for id (1217364077)
% 0.20/0.51  ipcrm: permission denied for id (1217396846)
% 0.20/0.51  ipcrm: permission denied for id (1220411503)
% 0.20/0.51  ipcrm: permission denied for id (1222082672)
% 0.20/0.51  ipcrm: permission denied for id (1222115441)
% 0.20/0.51  ipcrm: permission denied for id (1217495154)
% 0.20/0.51  ipcrm: permission denied for id (1222148211)
% 0.20/0.52  ipcrm: permission denied for id (1222180980)
% 0.20/0.52  ipcrm: permission denied for id (1222836341)
% 0.20/0.52  ipcrm: permission denied for id (1220608118)
% 0.20/0.52  ipcrm: permission denied for id (1217626231)
% 0.20/0.52  ipcrm: permission denied for id (1220640888)
% 0.20/0.52  ipcrm: permission denied for id (1217691769)
% 0.20/0.52  ipcrm: permission denied for id (1217724538)
% 0.20/0.53  ipcrm: permission denied for id (1223196795)
% 0.20/0.53  ipcrm: permission denied for id (1217790076)
% 0.20/0.53  ipcrm: permission denied for id (1217822845)
% 0.20/0.53  ipcrm: permission denied for id (1220706430)
% 0.38/0.61  % (23517)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.38/0.62  % (23511)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.64  % (23530)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.38/0.64  % (23522)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.66  % (23510)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.38/0.66  % (23521)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.38/0.67  % (23519)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.38/0.67  % (23524)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.38/0.67  % (23514)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.38/0.67  % (23518)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.38/0.67  % (23525)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.38/0.68  % (23526)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.38/0.68  % (23515)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.38/0.68  % (23527)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.38/0.68  % (23516)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.38/0.68  % (23513)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.38/0.69  % (23520)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.38/0.69  % (23523)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.38/0.69  % (23512)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.38/0.69  % (23529)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.38/0.70  % (23528)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.38/0.82  % (23517)Refutation found. Thanks to Tanya!
% 0.38/0.82  % SZS status Theorem for theBenchmark
% 0.38/0.82  % SZS output start Proof for theBenchmark
% 0.38/0.82  fof(f6565,plain,(
% 0.38/0.82    $false),
% 0.38/0.82    inference(avatar_sat_refutation,[],[f73,f78,f87,f92,f98,f108,f124,f129,f148,f156,f161,f181,f193,f198,f206,f222,f231,f238,f247,f260,f272,f277,f299,f308,f309,f316,f325,f347,f352,f389,f394,f413,f417,f420,f434,f446,f464,f468,f470,f472,f493,f512,f519,f528,f562,f567,f577,f610,f617,f642,f647,f668,f673,f682,f687,f697,f731,f752,f760,f769,f776,f1004,f1033,f1038,f1043,f1054,f1064,f1092,f1097,f1102,f1125,f1151,f1157,f1181,f1186,f1274,f1325,f1405,f1454,f1473,f1580,f1585,f1666,f1697,f1773,f1784,f1849,f1899,f1920,f1941,f1972,f2007,f2080,f2085,f2734,f2952,f2977,f3123,f3128,f3133,f3197,f3202,f3272,f3277,f3282,f3498,f3550,f5024,f5288,f5737,f5853,f5858,f5863,f5974,f6024,f6068,f6088,f6282,f6287,f6354,f6417,f6422,f6496,f6564])).
% 0.38/0.82  fof(f6564,plain,(
% 0.38/0.82    ~spl4_5 | spl4_107),
% 0.38/0.82    inference(avatar_contradiction_clause,[],[f6563])).
% 0.38/0.82  fof(f6563,plain,(
% 0.38/0.82    $false | (~spl4_5 | spl4_107)),
% 0.38/0.82    inference(subsumption_resolution,[],[f6562,f3933])).
% 0.38/0.82  fof(f3933,plain,(
% 0.38/0.82    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK0))) ) | ~spl4_5),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f97,f3761,f216])).
% 0.38/0.82  fof(f216,plain,(
% 0.38/0.82    ( ! [X8,X7,X9] : (~r1_tarski(X7,X8) | ~r1_tarski(X9,X7) | k1_xboole_0 = k4_xboole_0(X9,X8)) )),
% 0.38/0.82    inference(resolution,[],[f66,f61])).
% 0.38/0.82  fof(f61,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.38/0.82    inference(cnf_transformation,[],[f38])).
% 0.38/0.82  fof(f38,plain,(
% 0.38/0.82    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.38/0.82    inference(nnf_transformation,[],[f3])).
% 0.38/0.82  fof(f3,axiom,(
% 0.38/0.82    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.38/0.82  fof(f66,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f26])).
% 0.38/0.82  fof(f26,plain,(
% 0.38/0.82    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.38/0.82    inference(flattening,[],[f25])).
% 0.38/0.82  fof(f25,plain,(
% 0.38/0.82    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.38/0.82    inference(ennf_transformation,[],[f5])).
% 0.38/0.82  fof(f5,axiom,(
% 0.38/0.82    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.38/0.82  fof(f3761,plain,(
% 0.38/0.82    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f796,f60])).
% 0.38/0.82  fof(f60,plain,(
% 0.38/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f38])).
% 0.38/0.82  fof(f796,plain,(
% 0.38/0.82    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 0.38/0.82    inference(superposition,[],[f113,f62])).
% 0.38/0.82  fof(f62,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.38/0.82    inference(cnf_transformation,[],[f10])).
% 0.38/0.82  fof(f10,axiom,(
% 0.38/0.82    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.38/0.82  fof(f113,plain,(
% 0.38/0.82    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f44,f61])).
% 0.38/0.82  fof(f44,plain,(
% 0.38/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f7])).
% 0.38/0.82  fof(f7,axiom,(
% 0.38/0.82    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.38/0.82  fof(f97,plain,(
% 0.38/0.82    r1_tarski(sK1,sK0) | ~spl4_5),
% 0.38/0.82    inference(avatar_component_clause,[],[f95])).
% 0.38/0.82  fof(f95,plain,(
% 0.38/0.82    spl4_5 <=> r1_tarski(sK1,sK0)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.38/0.82  fof(f6562,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | spl4_107),
% 0.38/0.82    inference(forward_demodulation,[],[f6510,f46])).
% 0.38/0.82  fof(f46,plain,(
% 0.38/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.38/0.82    inference(cnf_transformation,[],[f9])).
% 0.38/0.82  fof(f9,axiom,(
% 0.38/0.82    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.38/0.82  fof(f6510,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))) | spl4_107),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f5973,f536])).
% 0.38/0.82  fof(f536,plain,(
% 0.38/0.82    ( ! [X14,X12,X13] : (k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14)) | r1_tarski(k4_xboole_0(X12,X13),X14)) )),
% 0.38/0.82    inference(superposition,[],[f60,f62])).
% 0.38/0.82  fof(f5973,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) | spl4_107),
% 0.38/0.82    inference(avatar_component_clause,[],[f5971])).
% 0.38/0.82  fof(f5971,plain,(
% 0.38/0.82    spl4_107 <=> r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 0.38/0.82  fof(f6496,plain,(
% 0.38/0.82    ~spl4_116 | spl4_114),
% 0.38/0.82    inference(avatar_split_clause,[],[f6424,f6414,f6493])).
% 0.38/0.82  fof(f6493,plain,(
% 0.38/0.82    spl4_116 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).
% 0.38/0.82  fof(f6414,plain,(
% 0.38/0.82    spl4_114 <=> r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).
% 0.38/0.82  fof(f6424,plain,(
% 0.38/0.82    ~m1_subset_1(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_114),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f6416,f47])).
% 0.38/0.82  fof(f47,plain,(
% 0.38/0.82    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f32])).
% 0.38/0.82  fof(f32,plain,(
% 0.38/0.82    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.38/0.82    inference(nnf_transformation,[],[f19])).
% 0.38/0.82  fof(f19,plain,(
% 0.38/0.82    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.38/0.82    inference(ennf_transformation,[],[f13])).
% 0.38/0.82  fof(f13,axiom,(
% 0.38/0.82    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.38/0.82  fof(f6416,plain,(
% 0.38/0.82    ~r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_114),
% 0.38/0.82    inference(avatar_component_clause,[],[f6414])).
% 0.38/0.82  fof(f43,plain,(
% 0.38/0.82    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.38/0.82    inference(cnf_transformation,[],[f15])).
% 0.38/0.82  fof(f15,axiom,(
% 0.38/0.82    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.38/0.82  fof(f6422,plain,(
% 0.38/0.82    ~spl4_115 | spl4_113),
% 0.38/0.82    inference(avatar_split_clause,[],[f6410,f6351,f6419])).
% 0.38/0.82  fof(f6419,plain,(
% 0.38/0.82    spl4_115 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 0.38/0.82  fof(f6351,plain,(
% 0.38/0.82    spl4_113 <=> r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 0.38/0.82  fof(f6410,plain,(
% 0.38/0.82    ~m1_subset_1(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_113),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f6353,f47])).
% 0.38/0.82  fof(f6353,plain,(
% 0.38/0.82    ~r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_113),
% 0.38/0.82    inference(avatar_component_clause,[],[f6351])).
% 0.38/0.82  fof(f6417,plain,(
% 0.38/0.82    ~spl4_114 | spl4_111),
% 0.38/0.82    inference(avatar_split_clause,[],[f6298,f6279,f6414])).
% 0.38/0.82  fof(f6279,plain,(
% 0.38/0.82    spl4_111 <=> r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).
% 0.38/0.82  fof(f6298,plain,(
% 0.38/0.82    ~r2_hidden(sK0,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_111),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f6281,f68])).
% 0.38/0.82  fof(f68,plain,(
% 0.38/0.82    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.38/0.82    inference(equality_resolution,[],[f56])).
% 0.38/0.82  fof(f56,plain,(
% 0.38/0.82    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.38/0.82    inference(cnf_transformation,[],[f37])).
% 0.38/0.82  fof(f37,plain,(
% 0.38/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.38/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.38/0.82  fof(f36,plain,(
% 0.38/0.82    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.38/0.82    introduced(choice_axiom,[])).
% 0.38/0.82  fof(f35,plain,(
% 0.38/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.38/0.82    inference(rectify,[],[f34])).
% 0.38/0.82  fof(f34,plain,(
% 0.38/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.38/0.82    inference(nnf_transformation,[],[f12])).
% 0.38/0.82  fof(f12,axiom,(
% 0.38/0.82    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.38/0.82  fof(f6281,plain,(
% 0.38/0.82    ~r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2)) | spl4_111),
% 0.38/0.82    inference(avatar_component_clause,[],[f6279])).
% 0.38/0.82  fof(f6354,plain,(
% 0.38/0.82    ~spl4_113 | spl4_106),
% 0.38/0.82    inference(avatar_split_clause,[],[f6209,f5860,f6351])).
% 0.38/0.82  fof(f5860,plain,(
% 0.38/0.82    spl4_106 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 0.38/0.82  fof(f6209,plain,(
% 0.38/0.82    ~r2_hidden(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2))) | spl4_106),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f5862,f116])).
% 0.38/0.82  fof(f116,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.38/0.82    inference(resolution,[],[f61,f68])).
% 0.38/0.82  fof(f5862,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2)) | spl4_106),
% 0.38/0.82    inference(avatar_component_clause,[],[f5860])).
% 0.38/0.82  fof(f6287,plain,(
% 0.38/0.82    ~spl4_112 | spl4_106),
% 0.38/0.82    inference(avatar_split_clause,[],[f6210,f5860,f6284])).
% 0.38/0.82  fof(f6284,plain,(
% 0.38/0.82    spl4_112 <=> r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 0.38/0.82  fof(f6210,plain,(
% 0.38/0.82    ~r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2)) | spl4_106),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f5862,f61])).
% 0.38/0.82  fof(f6282,plain,(
% 0.38/0.82    ~spl4_111 | ~spl4_5 | spl4_106),
% 0.38/0.82    inference(avatar_split_clause,[],[f6197,f5860,f95,f6279])).
% 0.38/0.82  fof(f6197,plain,(
% 0.38/0.82    ~r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK2)) | (~spl4_5 | spl4_106)),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f97,f5862,f216])).
% 0.38/0.82  fof(f6088,plain,(
% 0.38/0.82    ~spl4_110 | spl4_109),
% 0.38/0.82    inference(avatar_split_clause,[],[f6081,f6065,f6085])).
% 0.38/0.82  fof(f6085,plain,(
% 0.38/0.82    spl4_110 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).
% 0.38/0.82  fof(f6065,plain,(
% 0.38/0.82    spl4_109 <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 0.38/0.82  fof(f6081,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) | spl4_109),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f6067,f47])).
% 0.38/0.82  fof(f6067,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) | spl4_109),
% 0.38/0.82    inference(avatar_component_clause,[],[f6065])).
% 0.38/0.82  fof(f6068,plain,(
% 0.38/0.82    ~spl4_109 | spl4_42 | ~spl4_103),
% 0.38/0.82    inference(avatar_split_clause,[],[f6015,f5734,f607,f6065])).
% 0.38/0.82  fof(f607,plain,(
% 0.38/0.82    spl4_42 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.38/0.82  fof(f5734,plain,(
% 0.38/0.82    spl4_103 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 0.38/0.82  fof(f6015,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) | (spl4_42 | ~spl4_103)),
% 0.38/0.82    inference(subsumption_resolution,[],[f5995,f609])).
% 0.38/0.82  fof(f609,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK0,sK2) | spl4_42),
% 0.38/0.82    inference(avatar_component_clause,[],[f607])).
% 0.38/0.82  fof(f5995,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl4_103),
% 0.38/0.82    inference(superposition,[],[f111,f5736])).
% 0.38/0.82  fof(f5736,plain,(
% 0.38/0.82    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_103),
% 0.38/0.82    inference(avatar_component_clause,[],[f5734])).
% 0.38/0.82  fof(f111,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(k4_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 0.38/0.82    inference(resolution,[],[f53,f68])).
% 0.38/0.82  fof(f53,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.38/0.82    inference(cnf_transformation,[],[f22])).
% 0.38/0.82  fof(f22,plain,(
% 0.38/0.82    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.38/0.82    inference(ennf_transformation,[],[f8])).
% 0.38/0.82  fof(f8,axiom,(
% 0.38/0.82    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.38/0.82  fof(f6024,plain,(
% 0.38/0.82    ~spl4_108 | spl4_42 | ~spl4_103),
% 0.38/0.82    inference(avatar_split_clause,[],[f6014,f5734,f607,f6021])).
% 0.38/0.82  fof(f6021,plain,(
% 0.38/0.82    spl4_108 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 0.38/0.82  fof(f6014,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | (spl4_42 | ~spl4_103)),
% 0.38/0.82    inference(subsumption_resolution,[],[f5986,f609])).
% 0.38/0.82  fof(f5986,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl4_103),
% 0.38/0.82    inference(superposition,[],[f53,f5736])).
% 0.38/0.82  fof(f5974,plain,(
% 0.38/0.82    ~spl4_107 | ~spl4_32 | spl4_39),
% 0.38/0.82    inference(avatar_split_clause,[],[f3664,f559,f410,f5971])).
% 0.38/0.82  fof(f410,plain,(
% 0.38/0.82    spl4_32 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.38/0.82  fof(f559,plain,(
% 0.38/0.82    spl4_39 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.38/0.82  fof(f3664,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) | (~spl4_32 | spl4_39)),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f412,f2127,f66])).
% 0.38/0.82  fof(f2127,plain,(
% 0.38/0.82    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))) ) | spl4_39),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f561,f328,f214])).
% 0.38/0.82  fof(f214,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2) )),
% 0.38/0.82    inference(resolution,[],[f66,f53])).
% 0.38/0.82  fof(f328,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f44,f63])).
% 0.38/0.82  fof(f63,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f23])).
% 0.38/0.82  fof(f23,plain,(
% 0.38/0.82    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.38/0.82    inference(ennf_transformation,[],[f6])).
% 0.38/0.82  fof(f6,axiom,(
% 0.38/0.82    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.38/0.82  fof(f561,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl4_39),
% 0.38/0.82    inference(avatar_component_clause,[],[f559])).
% 0.38/0.82  fof(f412,plain,(
% 0.38/0.82    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_32),
% 0.38/0.82    inference(avatar_component_clause,[],[f410])).
% 0.38/0.82  fof(f5863,plain,(
% 0.38/0.82    ~spl4_106 | ~spl4_45 | spl4_81),
% 0.38/0.82    inference(avatar_split_clause,[],[f3110,f1896,f644,f5860])).
% 0.38/0.82  fof(f644,plain,(
% 0.38/0.82    spl4_45 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.38/0.82  fof(f1896,plain,(
% 0.38/0.82    spl4_81 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.38/0.82  fof(f3110,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK2)) | (~spl4_45 | spl4_81)),
% 0.38/0.82    inference(forward_demodulation,[],[f3109,f45])).
% 0.38/0.82  fof(f45,plain,(
% 0.38/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f1])).
% 0.38/0.82  fof(f1,axiom,(
% 0.38/0.82    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.38/0.82  fof(f3109,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0)) | (~spl4_45 | spl4_81)),
% 0.38/0.82    inference(forward_demodulation,[],[f3089,f1191])).
% 0.38/0.82  fof(f1191,plain,(
% 0.38/0.82    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1)) ) | ~spl4_45),
% 0.38/0.82    inference(superposition,[],[f46,f954])).
% 0.38/0.82  fof(f954,plain,(
% 0.38/0.82    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_45),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f904,f61])).
% 0.38/0.82  fof(f904,plain,(
% 0.38/0.82    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl4_45),
% 0.38/0.82    inference(backward_demodulation,[],[f651,f899])).
% 0.38/0.82  fof(f899,plain,(
% 0.38/0.82    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f839,f54])).
% 0.38/0.82  fof(f54,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.38/0.82    inference(cnf_transformation,[],[f33])).
% 0.38/0.82  fof(f33,plain,(
% 0.38/0.82    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.38/0.82    inference(nnf_transformation,[],[f11])).
% 0.38/0.82  fof(f11,axiom,(
% 0.38/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.38/0.82  fof(f839,plain,(
% 0.38/0.82    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f812,f51])).
% 0.38/0.82  fof(f51,plain,(
% 0.38/0.82    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f20])).
% 0.38/0.82  fof(f20,plain,(
% 0.38/0.82    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.38/0.82    inference(ennf_transformation,[],[f2])).
% 0.38/0.82  fof(f2,axiom,(
% 0.38/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.38/0.82  fof(f812,plain,(
% 0.38/0.82    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f798,f65])).
% 0.38/0.82  fof(f65,plain,(
% 0.38/0.82    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.38/0.82    inference(cnf_transformation,[],[f24])).
% 0.38/0.82  fof(f24,plain,(
% 0.38/0.82    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.38/0.82    inference(ennf_transformation,[],[f4])).
% 0.38/0.82  fof(f4,axiom,(
% 0.38/0.82    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.38/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.38/0.82  fof(f798,plain,(
% 0.38/0.82    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3))) )),
% 0.38/0.82    inference(superposition,[],[f44,f113])).
% 0.38/0.82  fof(f651,plain,(
% 0.38/0.82    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | ~spl4_45),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f646,f63])).
% 0.38/0.82  fof(f646,plain,(
% 0.38/0.82    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_45),
% 0.38/0.82    inference(avatar_component_clause,[],[f644])).
% 0.38/0.82  fof(f3089,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)) | spl4_81),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1898,f536])).
% 0.38/0.82  fof(f1898,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK1,sK2),sK2) | spl4_81),
% 0.38/0.82    inference(avatar_component_clause,[],[f1896])).
% 0.38/0.82  fof(f5858,plain,(
% 0.38/0.82    ~spl4_105 | spl4_81),
% 0.38/0.82    inference(avatar_split_clause,[],[f1911,f1896,f5855])).
% 0.38/0.82  fof(f5855,plain,(
% 0.38/0.82    spl4_105 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 0.38/0.82  fof(f1911,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),sK2) | spl4_81),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1898,f60])).
% 0.38/0.82  fof(f5853,plain,(
% 0.38/0.82    spl4_104 | ~spl4_65),
% 0.38/0.82    inference(avatar_split_clause,[],[f1250,f1122,f5850])).
% 0.38/0.82  fof(f5850,plain,(
% 0.38/0.82    spl4_104 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).
% 0.38/0.82  fof(f1122,plain,(
% 0.38/0.82    spl4_65 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.38/0.82  fof(f1250,plain,(
% 0.38/0.82    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl4_65),
% 0.38/0.82    inference(superposition,[],[f1124,f62])).
% 0.38/0.82  fof(f1124,plain,(
% 0.38/0.82    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_65),
% 0.38/0.82    inference(avatar_component_clause,[],[f1122])).
% 0.38/0.82  fof(f5737,plain,(
% 0.38/0.82    spl4_103 | ~spl4_41),
% 0.38/0.82    inference(avatar_split_clause,[],[f578,f574,f5734])).
% 0.38/0.82  fof(f574,plain,(
% 0.38/0.82    spl4_41 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.38/0.82  fof(f578,plain,(
% 0.38/0.82    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_41),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f576,f54])).
% 0.38/0.82  fof(f576,plain,(
% 0.38/0.82    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_41),
% 0.38/0.82    inference(avatar_component_clause,[],[f574])).
% 0.38/0.82  fof(f5288,plain,(
% 0.38/0.82    spl4_102 | ~spl4_40),
% 0.38/0.82    inference(avatar_split_clause,[],[f570,f564,f5285])).
% 0.38/0.82  fof(f5285,plain,(
% 0.38/0.82    spl4_102 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 0.38/0.82  fof(f564,plain,(
% 0.38/0.82    spl4_40 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.38/0.82  fof(f570,plain,(
% 0.38/0.82    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_40),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f566,f54])).
% 0.38/0.82  fof(f566,plain,(
% 0.38/0.82    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_40),
% 0.38/0.82    inference(avatar_component_clause,[],[f564])).
% 0.38/0.82  fof(f5024,plain,(
% 0.38/0.82    spl4_101 | ~spl4_56),
% 0.38/0.82    inference(avatar_split_clause,[],[f1049,f1001,f5021])).
% 0.38/0.82  fof(f5021,plain,(
% 0.38/0.82    spl4_101 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).
% 0.38/0.82  fof(f1001,plain,(
% 0.38/0.82    spl4_56 <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.38/0.82  fof(f1049,plain,(
% 0.38/0.82    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | ~spl4_56),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f1003,f48])).
% 0.38/0.82  fof(f48,plain,(
% 0.38/0.82    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.38/0.82    inference(cnf_transformation,[],[f32])).
% 0.38/0.82  fof(f1003,plain,(
% 0.38/0.82    r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | ~spl4_56),
% 0.38/0.82    inference(avatar_component_clause,[],[f1001])).
% 0.38/0.82  fof(f3550,plain,(
% 0.38/0.82    ~spl4_100 | spl4_99),
% 0.38/0.82    inference(avatar_split_clause,[],[f3515,f3495,f3547])).
% 0.38/0.82  fof(f3547,plain,(
% 0.38/0.82    spl4_100 <=> m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 0.38/0.82  fof(f3495,plain,(
% 0.38/0.82    spl4_99 <=> r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2)))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 0.38/0.82  fof(f3515,plain,(
% 0.38/0.82    ~m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2))) | spl4_99),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f3497,f47])).
% 0.38/0.82  fof(f3497,plain,(
% 0.38/0.82    ~r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2))) | spl4_99),
% 0.38/0.82    inference(avatar_component_clause,[],[f3495])).
% 0.38/0.82  fof(f3498,plain,(
% 0.38/0.82    ~spl4_99 | spl4_70),
% 0.38/0.82    inference(avatar_split_clause,[],[f1301,f1271,f3495])).
% 0.38/0.82  fof(f1271,plain,(
% 0.38/0.82    spl4_70 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.38/0.82  fof(f1301,plain,(
% 0.38/0.82    ~r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK2))) | spl4_70),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1273,f68])).
% 0.38/0.82  fof(f1273,plain,(
% 0.38/0.82    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl4_70),
% 0.38/0.82    inference(avatar_component_clause,[],[f1271])).
% 0.38/0.82  fof(f3282,plain,(
% 0.38/0.82    ~spl4_98 | spl4_93),
% 0.38/0.82    inference(avatar_split_clause,[],[f3228,f3130,f3279])).
% 0.38/0.82  fof(f3279,plain,(
% 0.38/0.82    spl4_98 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 0.38/0.82  fof(f3130,plain,(
% 0.38/0.82    spl4_93 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 0.38/0.82  fof(f3228,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2)) | spl4_93),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f3132,f47])).
% 0.38/0.82  fof(f3132,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2)) | spl4_93),
% 0.38/0.82    inference(avatar_component_clause,[],[f3130])).
% 0.38/0.82  fof(f3277,plain,(
% 0.38/0.82    ~spl4_97 | spl4_92),
% 0.38/0.82    inference(avatar_split_clause,[],[f3208,f3125,f3274])).
% 0.38/0.82  fof(f3274,plain,(
% 0.38/0.82    spl4_97 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 0.38/0.82  fof(f3125,plain,(
% 0.38/0.82    spl4_92 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 0.38/0.82  fof(f3208,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | spl4_92),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f3127,f47])).
% 0.38/0.82  fof(f3127,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | spl4_92),
% 0.38/0.82    inference(avatar_component_clause,[],[f3125])).
% 0.38/0.82  fof(f3272,plain,(
% 0.38/0.82    ~spl4_96 | spl4_91),
% 0.38/0.82    inference(avatar_split_clause,[],[f3204,f3120,f3269])).
% 0.38/0.82  fof(f3269,plain,(
% 0.38/0.82    spl4_96 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 0.38/0.82  fof(f3120,plain,(
% 0.38/0.82    spl4_91 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 0.38/0.82  fof(f3204,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_91),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f3122,f47])).
% 0.38/0.82  fof(f3122,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_91),
% 0.38/0.82    inference(avatar_component_clause,[],[f3120])).
% 0.38/0.82  fof(f3202,plain,(
% 0.38/0.82    ~spl4_95 | spl4_90),
% 0.38/0.82    inference(avatar_split_clause,[],[f3041,f2974,f3199])).
% 0.38/0.82  fof(f3199,plain,(
% 0.38/0.82    spl4_95 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).
% 0.38/0.82  fof(f2974,plain,(
% 0.38/0.82    spl4_90 <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 0.38/0.82  fof(f3041,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2)) | spl4_90),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f2976,f47])).
% 0.38/0.82  fof(f2976,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2)) | spl4_90),
% 0.38/0.82    inference(avatar_component_clause,[],[f2974])).
% 0.38/0.82  fof(f3197,plain,(
% 0.38/0.82    ~spl4_94 | spl4_89),
% 0.38/0.82    inference(avatar_split_clause,[],[f3037,f2949,f3194])).
% 0.38/0.82  fof(f3194,plain,(
% 0.38/0.82    spl4_94 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 0.38/0.82  fof(f2949,plain,(
% 0.38/0.82    spl4_89 <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 0.38/0.82  fof(f3037,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_89),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f2951,f47])).
% 0.38/0.82  fof(f2951,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_89),
% 0.38/0.82    inference(avatar_component_clause,[],[f2949])).
% 0.38/0.82  fof(f3133,plain,(
% 0.38/0.82    ~spl4_93 | spl4_84),
% 0.38/0.82    inference(avatar_split_clause,[],[f1999,f1969,f3130])).
% 0.38/0.82  fof(f1969,plain,(
% 0.38/0.82    spl4_84 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 0.38/0.82  fof(f1999,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK2)) | spl4_84),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1971,f68])).
% 0.38/0.82  fof(f1971,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2) | spl4_84),
% 0.38/0.82    inference(avatar_component_clause,[],[f1969])).
% 0.38/0.82  fof(f3128,plain,(
% 0.38/0.82    ~spl4_92 | spl4_83),
% 0.38/0.82    inference(avatar_split_clause,[],[f1984,f1938,f3125])).
% 0.38/0.82  fof(f1938,plain,(
% 0.38/0.82    spl4_83 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 0.38/0.82  fof(f1984,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | spl4_83),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1940,f68])).
% 0.38/0.82  fof(f1940,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl4_83),
% 0.38/0.82    inference(avatar_component_clause,[],[f1938])).
% 0.38/0.82  fof(f3123,plain,(
% 0.38/0.82    ~spl4_91 | spl4_74),
% 0.38/0.82    inference(avatar_split_clause,[],[f1482,f1470,f3120])).
% 0.38/0.82  fof(f1470,plain,(
% 0.38/0.82    spl4_74 <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.38/0.82  fof(f1482,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_74),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1472,f68])).
% 0.38/0.82  fof(f1472,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl4_74),
% 0.38/0.82    inference(avatar_component_clause,[],[f1470])).
% 0.38/0.82  fof(f2977,plain,(
% 0.38/0.82    ~spl4_90 | spl4_82),
% 0.38/0.82    inference(avatar_split_clause,[],[f1933,f1917,f2974])).
% 0.38/0.82  fof(f1917,plain,(
% 0.38/0.82    spl4_82 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.38/0.82  fof(f1933,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK2)) | spl4_82),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1919,f68])).
% 0.38/0.82  fof(f1919,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),sK2) | spl4_82),
% 0.38/0.82    inference(avatar_component_clause,[],[f1917])).
% 0.38/0.82  fof(f2952,plain,(
% 0.38/0.82    ~spl4_89 | spl4_73),
% 0.38/0.82    inference(avatar_split_clause,[],[f1464,f1451,f2949])).
% 0.38/0.82  fof(f1451,plain,(
% 0.38/0.82    spl4_73 <=> r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.38/0.82  fof(f1464,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_73),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1453,f68])).
% 0.38/0.82  fof(f1453,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | spl4_73),
% 0.38/0.82    inference(avatar_component_clause,[],[f1451])).
% 0.38/0.82  fof(f2734,plain,(
% 0.38/0.82    ~spl4_88 | spl4_86),
% 0.38/0.82    inference(avatar_split_clause,[],[f2254,f2077,f2731])).
% 0.38/0.82  fof(f2731,plain,(
% 0.38/0.82    spl4_88 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 0.38/0.82  fof(f2077,plain,(
% 0.38/0.82    spl4_86 <=> r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 0.38/0.82  fof(f2254,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_86),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f2079,f47])).
% 0.38/0.82  fof(f2079,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_86),
% 0.38/0.82    inference(avatar_component_clause,[],[f2077])).
% 0.38/0.82  fof(f2085,plain,(
% 0.38/0.82    ~spl4_87 | spl4_85),
% 0.38/0.82    inference(avatar_split_clause,[],[f2009,f2004,f2082])).
% 0.38/0.82  fof(f2082,plain,(
% 0.38/0.82    spl4_87 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 0.38/0.82  fof(f2004,plain,(
% 0.38/0.82    spl4_85 <=> r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 0.38/0.82  fof(f2009,plain,(
% 0.38/0.82    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) | spl4_85),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f43,f2006,f47])).
% 0.38/0.82  fof(f2006,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) | spl4_85),
% 0.38/0.82    inference(avatar_component_clause,[],[f2004])).
% 0.38/0.82  fof(f2080,plain,(
% 0.38/0.82    ~spl4_86 | spl4_72),
% 0.38/0.82    inference(avatar_split_clause,[],[f1445,f1402,f2077])).
% 0.38/0.82  fof(f1402,plain,(
% 0.38/0.82    spl4_72 <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.38/0.82  fof(f1445,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_72),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1404,f68])).
% 0.38/0.82  fof(f1404,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | spl4_72),
% 0.38/0.82    inference(avatar_component_clause,[],[f1402])).
% 0.38/0.82  fof(f2007,plain,(
% 0.38/0.82    ~spl4_85 | spl4_81),
% 0.38/0.82    inference(avatar_split_clause,[],[f1912,f1896,f2004])).
% 0.38/0.82  fof(f1912,plain,(
% 0.38/0.82    ~r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) | spl4_81),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f1898,f68])).
% 0.38/0.82  fof(f1972,plain,(
% 0.38/0.82    ~spl4_84 | ~spl4_32 | spl4_82),
% 0.38/0.82    inference(avatar_split_clause,[],[f1928,f1917,f410,f1969])).
% 0.38/0.82  fof(f1928,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl4_32 | spl4_82)),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f412,f1919,f66])).
% 0.38/0.82  fof(f1941,plain,(
% 0.38/0.82    ~spl4_83 | spl4_51),
% 0.38/0.82    inference(avatar_split_clause,[],[f1867,f728,f1938])).
% 0.38/0.82  fof(f728,plain,(
% 0.38/0.82    spl4_51 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.38/0.82  fof(f1867,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl4_51),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f730,f335])).
% 0.38/0.82  fof(f335,plain,(
% 0.38/0.82    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.38/0.82    inference(resolution,[],[f63,f53])).
% 0.38/0.82  fof(f730,plain,(
% 0.38/0.82    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl4_51),
% 0.38/0.82    inference(avatar_component_clause,[],[f728])).
% 0.38/0.82  fof(f1920,plain,(
% 0.38/0.82    ~spl4_82 | spl4_42),
% 0.38/0.82    inference(avatar_split_clause,[],[f1866,f607,f1917])).
% 0.38/0.82  fof(f1866,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),sK2) | spl4_42),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f609,f335])).
% 0.38/0.82  fof(f1899,plain,(
% 0.38/0.82    ~spl4_81 | spl4_39),
% 0.38/0.82    inference(avatar_split_clause,[],[f1865,f559,f1896])).
% 0.38/0.82  fof(f1865,plain,(
% 0.38/0.82    ~r1_tarski(k4_xboole_0(sK1,sK2),sK2) | spl4_39),
% 0.38/0.82    inference(unit_resulting_resolution,[],[f561,f335])).
% 0.38/0.82  fof(f1849,plain,(
% 0.38/0.82    ~spl4_80 | spl4_79),
% 0.38/0.82    inference(avatar_split_clause,[],[f1819,f1781,f1846])).
% 0.38/0.82  fof(f1846,plain,(
% 0.38/0.82    spl4_80 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.38/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 0.39/0.82  fof(f1781,plain,(
% 0.39/0.82    spl4_79 <=> r1_xboole_0(sK0,sK2)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 0.39/0.82  fof(f1819,plain,(
% 0.39/0.82    sK0 != k4_xboole_0(sK0,sK2) | spl4_79),
% 0.39/0.82    inference(unit_resulting_resolution,[],[f1783,f55])).
% 0.39/0.82  fof(f55,plain,(
% 0.39/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.39/0.82    inference(cnf_transformation,[],[f33])).
% 0.39/0.82  fof(f1783,plain,(
% 0.39/0.82    ~r1_xboole_0(sK0,sK2) | spl4_79),
% 0.39/0.82    inference(avatar_component_clause,[],[f1781])).
% 0.39/0.82  fof(f1784,plain,(
% 0.39/0.82    ~spl4_79 | spl4_78),
% 0.39/0.82    inference(avatar_split_clause,[],[f1776,f1770,f1781])).
% 0.39/0.82  fof(f1770,plain,(
% 0.39/0.82    spl4_78 <=> r1_xboole_0(sK2,sK0)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 0.39/0.82  fof(f1776,plain,(
% 0.39/0.82    ~r1_xboole_0(sK0,sK2) | spl4_78),
% 0.39/0.82    inference(unit_resulting_resolution,[],[f1771,f51])).
% 0.39/0.82  fof(f1771,plain,(
% 0.39/0.82    ~r1_xboole_0(sK2,sK0) | spl4_78),
% 0.39/0.82    inference(avatar_component_clause,[],[f1770])).
% 0.39/0.82  fof(f1773,plain,(
% 0.39/0.82    spl4_78 | ~spl4_66 | ~spl4_8),
% 0.39/0.82    inference(avatar_split_clause,[],[f171,f126,f1148,f1770])).
% 0.39/0.82  fof(f1148,plain,(
% 0.39/0.82    spl4_66 <=> k1_xboole_0 = sK2),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.39/0.82  fof(f126,plain,(
% 0.39/0.82    spl4_8 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.39/0.82  fof(f171,plain,(
% 0.39/0.82    k1_xboole_0 != sK2 | r1_xboole_0(sK2,sK0) | ~spl4_8),
% 0.39/0.82    inference(superposition,[],[f55,f128])).
% 0.39/0.82  fof(f128,plain,(
% 0.39/0.82    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl4_8),
% 0.39/0.82    inference(avatar_component_clause,[],[f126])).
% 0.39/0.82  fof(f1697,plain,(
% 0.39/0.82    ~spl4_77 | spl4_76),
% 0.39/0.82    inference(avatar_split_clause,[],[f1668,f1663,f1694])).
% 0.39/0.82  fof(f1694,plain,(
% 0.39/0.82    spl4_77 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 0.39/0.82  fof(f1663,plain,(
% 0.39/0.82    spl4_76 <=> r1_xboole_0(sK0,sK1)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.39/0.82  fof(f1668,plain,(
% 0.39/0.82    sK0 != k4_xboole_0(sK0,sK1) | spl4_76),
% 0.39/0.82    inference(unit_resulting_resolution,[],[f1665,f55])).
% 0.39/0.82  fof(f1665,plain,(
% 0.39/0.82    ~r1_xboole_0(sK0,sK1) | spl4_76),
% 0.39/0.82    inference(avatar_component_clause,[],[f1663])).
% 0.39/0.82  fof(f1666,plain,(
% 0.39/0.82    ~spl4_76 | spl4_75),
% 0.39/0.82    inference(avatar_split_clause,[],[f1658,f1582,f1663])).
% 0.39/0.82  fof(f1582,plain,(
% 0.39/0.82    spl4_75 <=> r1_xboole_0(sK1,sK0)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.39/0.82  fof(f1658,plain,(
% 0.39/0.82    ~r1_xboole_0(sK0,sK1) | spl4_75),
% 0.39/0.82    inference(unit_resulting_resolution,[],[f1583,f51])).
% 0.39/0.82  fof(f1583,plain,(
% 0.39/0.82    ~r1_xboole_0(sK1,sK0) | spl4_75),
% 0.39/0.82    inference(avatar_component_clause,[],[f1582])).
% 0.39/0.82  fof(f1585,plain,(
% 0.39/0.82    spl4_75 | ~spl4_60 | ~spl4_7),
% 0.39/0.82    inference(avatar_split_clause,[],[f138,f121,f1051,f1582])).
% 0.39/0.82  fof(f1051,plain,(
% 0.39/0.82    spl4_60 <=> k1_xboole_0 = sK1),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.39/0.82  fof(f121,plain,(
% 0.39/0.82    spl4_7 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.39/0.82  fof(f138,plain,(
% 0.39/0.82    k1_xboole_0 != sK1 | r1_xboole_0(sK1,sK0) | ~spl4_7),
% 0.39/0.82    inference(superposition,[],[f55,f123])).
% 0.39/0.82  fof(f123,plain,(
% 0.39/0.82    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl4_7),
% 0.39/0.82    inference(avatar_component_clause,[],[f121])).
% 0.39/0.82  fof(f1580,plain,(
% 0.39/0.82    spl4_61 | ~spl4_23 | ~spl4_7),
% 0.39/0.82    inference(avatar_split_clause,[],[f137,f121,f274,f1061])).
% 0.39/0.82  fof(f1061,plain,(
% 0.39/0.82    spl4_61 <=> k1_xboole_0 = sK0),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.39/0.82  fof(f274,plain,(
% 0.39/0.82    spl4_23 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.39/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.39/0.82  fof(f137,plain,(
% 0.39/0.82    ~r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl4_7),
% 0.39/0.82    inference(superposition,[],[f53,f123])).
% 0.39/0.82  fof(f1473,plain,(
% 0.39/0.82    ~spl4_74 | spl4_51),
% 0.39/0.82    inference(avatar_split_clause,[],[f1381,f728,f1470])).
% 0.39/0.83  fof(f1381,plain,(
% 0.39/0.83    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl4_51),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f730,f800])).
% 0.39/0.83  fof(f800,plain,(
% 0.39/0.83    ( ! [X6] : (~r1_tarski(X6,k1_xboole_0) | k1_xboole_0 = X6) )),
% 0.39/0.83    inference(superposition,[],[f53,f113])).
% 0.39/0.83  fof(f1454,plain,(
% 0.39/0.83    ~spl4_73 | spl4_42),
% 0.39/0.83    inference(avatar_split_clause,[],[f1380,f607,f1451])).
% 0.39/0.83  fof(f1380,plain,(
% 0.39/0.83    ~r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | spl4_42),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f609,f800])).
% 0.39/0.83  fof(f1405,plain,(
% 0.39/0.83    ~spl4_72 | spl4_39),
% 0.39/0.83    inference(avatar_split_clause,[],[f1379,f559,f1402])).
% 0.39/0.83  fof(f1379,plain,(
% 0.39/0.83    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | spl4_39),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f561,f800])).
% 0.39/0.83  fof(f1325,plain,(
% 0.39/0.83    ~spl4_71 | ~spl4_5 | ~spl4_32 | ~spl4_46 | spl4_58),
% 0.39/0.83    inference(avatar_split_clause,[],[f1232,f1035,f665,f410,f95,f1322])).
% 0.39/0.83  fof(f1322,plain,(
% 0.39/0.83    spl4_71 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.39/0.83  fof(f665,plain,(
% 0.39/0.83    spl4_46 <=> r1_xboole_0(sK1,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.39/0.83  fof(f1035,plain,(
% 0.39/0.83    spl4_58 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.39/0.83  fof(f1232,plain,(
% 0.39/0.83    ~r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_5 | ~spl4_32 | ~spl4_46 | spl4_58)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f412,f1103,f66])).
% 0.39/0.83  fof(f1103,plain,(
% 0.39/0.83    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,sK1))) ) | (~spl4_5 | ~spl4_46 | spl4_58)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f97,f1047,f66])).
% 0.39/0.83  fof(f1047,plain,(
% 0.39/0.83    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,sK1))) ) | (~spl4_46 | spl4_58)),
% 0.39/0.83    inference(forward_demodulation,[],[f1044,f674])).
% 0.39/0.83  fof(f674,plain,(
% 0.39/0.83    sK1 = k4_xboole_0(sK1,k1_xboole_0) | ~spl4_46),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f667,f54])).
% 0.39/0.83  fof(f667,plain,(
% 0.39/0.83    r1_xboole_0(sK1,k1_xboole_0) | ~spl4_46),
% 0.39/0.83    inference(avatar_component_clause,[],[f665])).
% 0.39/0.83  fof(f1044,plain,(
% 0.39/0.83    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(sK1,k1_xboole_0)))) ) | spl4_58),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f1037,f53])).
% 0.39/0.83  fof(f1037,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) | spl4_58),
% 0.39/0.83    inference(avatar_component_clause,[],[f1035])).
% 0.39/0.83  fof(f1274,plain,(
% 0.39/0.83    ~spl4_70 | ~spl4_32 | ~spl4_46 | spl4_58),
% 0.39/0.83    inference(avatar_split_clause,[],[f1106,f1035,f665,f410,f1271])).
% 0.39/0.83  fof(f1106,plain,(
% 0.39/0.83    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_32 | ~spl4_46 | spl4_58)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f412,f1047,f66])).
% 0.39/0.83  fof(f1186,plain,(
% 0.39/0.83    spl4_69 | ~spl4_18),
% 0.39/0.83    inference(avatar_split_clause,[],[f908,f235,f1183])).
% 0.39/0.83  fof(f1183,plain,(
% 0.39/0.83    spl4_69 <=> sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.39/0.83  fof(f235,plain,(
% 0.39/0.83    spl4_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.39/0.83  fof(f908,plain,(
% 0.39/0.83    sK0 = k3_subset_1(sK0,k1_xboole_0) | ~spl4_18),
% 0.39/0.83    inference(backward_demodulation,[],[f365,f899])).
% 0.39/0.83  fof(f365,plain,(
% 0.39/0.83    k4_xboole_0(sK0,k1_xboole_0) = k3_subset_1(sK0,k1_xboole_0) | ~spl4_18),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f237,f52])).
% 0.39/0.83  fof(f52,plain,(
% 0.39/0.83    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.39/0.83    inference(cnf_transformation,[],[f21])).
% 0.39/0.83  fof(f21,plain,(
% 0.39/0.83    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.83    inference(ennf_transformation,[],[f14])).
% 0.39/0.83  fof(f14,axiom,(
% 0.39/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.39/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.39/0.83  fof(f237,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_18),
% 0.39/0.83    inference(avatar_component_clause,[],[f235])).
% 0.39/0.83  fof(f1181,plain,(
% 0.39/0.83    spl4_68 | ~spl4_53),
% 0.39/0.83    inference(avatar_split_clause,[],[f761,f757,f1178])).
% 0.39/0.83  fof(f1178,plain,(
% 0.39/0.83    spl4_68 <=> sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.39/0.83  fof(f757,plain,(
% 0.39/0.83    spl4_53 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.39/0.83  fof(f761,plain,(
% 0.39/0.83    sK2 = k4_xboole_0(sK2,k1_xboole_0) | ~spl4_53),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f759,f54])).
% 0.39/0.83  fof(f759,plain,(
% 0.39/0.83    r1_xboole_0(sK2,k1_xboole_0) | ~spl4_53),
% 0.39/0.83    inference(avatar_component_clause,[],[f757])).
% 0.39/0.83  fof(f1157,plain,(
% 0.39/0.83    spl4_67 | ~spl4_46),
% 0.39/0.83    inference(avatar_split_clause,[],[f674,f665,f1154])).
% 0.39/0.83  fof(f1154,plain,(
% 0.39/0.83    spl4_67 <=> sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.39/0.83  fof(f1151,plain,(
% 0.39/0.83    ~spl4_66 | spl4_62),
% 0.39/0.83    inference(avatar_split_clause,[],[f1145,f1089,f1148])).
% 0.39/0.83  fof(f1089,plain,(
% 0.39/0.83    spl4_62 <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.39/0.83  fof(f1145,plain,(
% 0.39/0.83    k1_xboole_0 != sK2 | spl4_62),
% 0.39/0.83    inference(superposition,[],[f1091,f899])).
% 0.39/0.83  fof(f1091,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0) | spl4_62),
% 0.39/0.83    inference(avatar_component_clause,[],[f1089])).
% 0.39/0.83  fof(f1125,plain,(
% 0.39/0.83    spl4_65 | ~spl4_32),
% 0.39/0.83    inference(avatar_split_clause,[],[f503,f410,f1122])).
% 0.39/0.83  fof(f503,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_32),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f412,f61])).
% 0.39/0.83  fof(f1102,plain,(
% 0.39/0.83    spl4_64 | ~spl4_45 | ~spl4_49),
% 0.39/0.83    inference(avatar_split_clause,[],[f692,f684,f644,f1099])).
% 0.39/0.83  fof(f1099,plain,(
% 0.39/0.83    spl4_64 <=> k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.39/0.83  fof(f684,plain,(
% 0.39/0.83    spl4_49 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.39/0.83  fof(f692,plain,(
% 0.39/0.83    k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0) | (~spl4_45 | ~spl4_49)),
% 0.39/0.83    inference(forward_demodulation,[],[f690,f661])).
% 0.39/0.83  fof(f661,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_45),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f646,f61])).
% 0.39/0.83  fof(f690,plain,(
% 0.39/0.83    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_subset_1(k1_xboole_0,k1_xboole_0) | ~spl4_49),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f686,f52])).
% 0.39/0.83  fof(f686,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_49),
% 0.39/0.83    inference(avatar_component_clause,[],[f684])).
% 0.39/0.83  fof(f1097,plain,(
% 0.39/0.83    spl4_63 | ~spl4_45),
% 0.39/0.83    inference(avatar_split_clause,[],[f661,f644,f1094])).
% 0.39/0.83  fof(f1094,plain,(
% 0.39/0.83    spl4_63 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.39/0.83  fof(f1092,plain,(
% 0.39/0.83    ~spl4_62 | spl4_34),
% 0.39/0.83    inference(avatar_split_clause,[],[f450,f443,f1089])).
% 0.39/0.83  fof(f443,plain,(
% 0.39/0.83    spl4_34 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.39/0.83  fof(f450,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0) | spl4_34),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f445,f60])).
% 0.39/0.83  fof(f445,plain,(
% 0.39/0.83    ~r1_tarski(sK2,k1_xboole_0) | spl4_34),
% 0.39/0.83    inference(avatar_component_clause,[],[f443])).
% 0.39/0.83  fof(f1064,plain,(
% 0.39/0.83    ~spl4_61 | spl4_59),
% 0.39/0.83    inference(avatar_split_clause,[],[f1058,f1040,f1061])).
% 0.39/0.83  fof(f1040,plain,(
% 0.39/0.83    spl4_59 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.39/0.83  fof(f1058,plain,(
% 0.39/0.83    k1_xboole_0 != sK0 | spl4_59),
% 0.39/0.83    inference(superposition,[],[f1042,f899])).
% 0.39/0.83  fof(f1042,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | spl4_59),
% 0.39/0.83    inference(avatar_component_clause,[],[f1040])).
% 0.39/0.83  fof(f1054,plain,(
% 0.39/0.83    ~spl4_60 | spl4_58),
% 0.39/0.83    inference(avatar_split_clause,[],[f1046,f1035,f1051])).
% 0.39/0.83  fof(f1046,plain,(
% 0.39/0.83    k1_xboole_0 != sK1 | spl4_58),
% 0.39/0.83    inference(superposition,[],[f1037,f899])).
% 0.39/0.83  fof(f1043,plain,(
% 0.39/0.83    ~spl4_59 | spl4_23),
% 0.39/0.83    inference(avatar_split_clause,[],[f291,f274,f1040])).
% 0.39/0.83  fof(f291,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | spl4_23),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f276,f60])).
% 0.39/0.83  fof(f276,plain,(
% 0.39/0.83    ~r1_tarski(sK0,k1_xboole_0) | spl4_23),
% 0.39/0.83    inference(avatar_component_clause,[],[f274])).
% 0.39/0.83  fof(f1038,plain,(
% 0.39/0.83    ~spl4_58 | spl4_22),
% 0.39/0.83    inference(avatar_split_clause,[],[f285,f269,f1035])).
% 0.39/0.83  fof(f269,plain,(
% 0.39/0.83    spl4_22 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.39/0.83  fof(f285,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) | spl4_22),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f271,f60])).
% 0.39/0.83  fof(f271,plain,(
% 0.39/0.83    ~r1_tarski(sK1,k1_xboole_0) | spl4_22),
% 0.39/0.83    inference(avatar_component_clause,[],[f269])).
% 0.39/0.83  fof(f1033,plain,(
% 0.39/0.83    spl4_57 | ~spl4_16),
% 0.39/0.83    inference(avatar_split_clause,[],[f224,f219,f1030])).
% 0.39/0.83  fof(f1030,plain,(
% 0.39/0.83    spl4_57 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.39/0.83  fof(f219,plain,(
% 0.39/0.83    spl4_16 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.39/0.83  fof(f224,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl4_16),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f221,f61])).
% 0.39/0.83  fof(f221,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK0) | ~spl4_16),
% 0.39/0.83    inference(avatar_component_clause,[],[f219])).
% 0.39/0.83  fof(f1004,plain,(
% 0.39/0.83    spl4_56 | ~spl4_32),
% 0.39/0.83    inference(avatar_split_clause,[],[f504,f410,f1001])).
% 0.39/0.83  fof(f504,plain,(
% 0.39/0.83    r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | ~spl4_32),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f412,f67])).
% 0.39/0.83  fof(f67,plain,(
% 0.39/0.83    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.39/0.83    inference(equality_resolution,[],[f57])).
% 0.39/0.83  fof(f57,plain,(
% 0.39/0.83    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.39/0.83    inference(cnf_transformation,[],[f37])).
% 0.39/0.83  fof(f776,plain,(
% 0.39/0.83    spl4_55 | ~spl4_14 | ~spl4_53),
% 0.39/0.83    inference(avatar_split_clause,[],[f764,f757,f195,f773])).
% 0.39/0.83  fof(f773,plain,(
% 0.39/0.83    spl4_55 <=> sK2 = k3_subset_1(sK2,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.39/0.83  fof(f195,plain,(
% 0.39/0.83    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.39/0.83  fof(f764,plain,(
% 0.39/0.83    sK2 = k3_subset_1(sK2,k1_xboole_0) | (~spl4_14 | ~spl4_53)),
% 0.39/0.83    inference(backward_demodulation,[],[f367,f761])).
% 0.39/0.83  fof(f367,plain,(
% 0.39/0.83    k4_xboole_0(sK2,k1_xboole_0) = k3_subset_1(sK2,k1_xboole_0) | ~spl4_14),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f197,f52])).
% 0.39/0.83  fof(f197,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | ~spl4_14),
% 0.39/0.83    inference(avatar_component_clause,[],[f195])).
% 0.39/0.83  fof(f769,plain,(
% 0.39/0.83    spl4_54 | ~spl4_11 | ~spl4_46),
% 0.39/0.83    inference(avatar_split_clause,[],[f677,f665,f158,f766])).
% 0.39/0.83  fof(f766,plain,(
% 0.39/0.83    spl4_54 <=> sK1 = k3_subset_1(sK1,k1_xboole_0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.39/0.83  fof(f158,plain,(
% 0.39/0.83    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.39/0.83  fof(f677,plain,(
% 0.39/0.83    sK1 = k3_subset_1(sK1,k1_xboole_0) | (~spl4_11 | ~spl4_46)),
% 0.39/0.83    inference(backward_demodulation,[],[f366,f674])).
% 0.39/0.83  fof(f366,plain,(
% 0.39/0.83    k4_xboole_0(sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) | ~spl4_11),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f160,f52])).
% 0.39/0.83  fof(f160,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl4_11),
% 0.39/0.83    inference(avatar_component_clause,[],[f158])).
% 0.39/0.83  fof(f760,plain,(
% 0.39/0.83    spl4_53 | ~spl4_52),
% 0.39/0.83    inference(avatar_split_clause,[],[f754,f749,f757])).
% 0.39/0.83  fof(f749,plain,(
% 0.39/0.83    spl4_52 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.39/0.83  fof(f754,plain,(
% 0.39/0.83    r1_xboole_0(sK2,k1_xboole_0) | ~spl4_52),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f751,f51])).
% 0.39/0.83  fof(f751,plain,(
% 0.39/0.83    r1_xboole_0(k1_xboole_0,sK2) | ~spl4_52),
% 0.39/0.83    inference(avatar_component_clause,[],[f749])).
% 0.39/0.83  fof(f752,plain,(
% 0.39/0.83    spl4_52 | ~spl4_43),
% 0.39/0.83    inference(avatar_split_clause,[],[f733,f614,f749])).
% 0.39/0.83  fof(f614,plain,(
% 0.39/0.83    spl4_43 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.39/0.83  fof(f733,plain,(
% 0.39/0.83    r1_xboole_0(k1_xboole_0,sK2) | ~spl4_43),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f616,f55])).
% 0.39/0.83  fof(f616,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl4_43),
% 0.39/0.83    inference(avatar_component_clause,[],[f614])).
% 0.39/0.83  fof(f731,plain,(
% 0.39/0.83    ~spl4_51 | spl4_33),
% 0.39/0.83    inference(avatar_split_clause,[],[f438,f431,f728])).
% 0.39/0.83  fof(f431,plain,(
% 0.39/0.83    spl4_33 <=> r1_tarski(sK0,sK1)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.39/0.83  fof(f438,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl4_33),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f433,f60])).
% 0.39/0.83  fof(f433,plain,(
% 0.39/0.83    ~r1_tarski(sK0,sK1) | spl4_33),
% 0.39/0.83    inference(avatar_component_clause,[],[f431])).
% 0.39/0.83  fof(f697,plain,(
% 0.39/0.83    spl4_50 | ~spl4_2),
% 0.39/0.83    inference(avatar_split_clause,[],[f364,f75,f694])).
% 0.39/0.83  fof(f694,plain,(
% 0.39/0.83    spl4_50 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.39/0.83  fof(f75,plain,(
% 0.39/0.83    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.39/0.83  fof(f364,plain,(
% 0.39/0.83    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_2),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f77,f52])).
% 0.39/0.83  fof(f77,plain,(
% 0.39/0.83    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.39/0.83    inference(avatar_component_clause,[],[f75])).
% 0.39/0.83  fof(f687,plain,(
% 0.39/0.83    spl4_49 | ~spl4_15),
% 0.39/0.83    inference(avatar_split_clause,[],[f629,f203,f684])).
% 0.39/0.83  fof(f203,plain,(
% 0.39/0.83    spl4_15 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.39/0.83  fof(f629,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_15),
% 0.39/0.83    inference(superposition,[],[f100,f205])).
% 0.39/0.83  fof(f205,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl4_15),
% 0.39/0.83    inference(avatar_component_clause,[],[f203])).
% 0.39/0.83  fof(f100,plain,(
% 0.39/0.83    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f79,f48])).
% 0.39/0.83  fof(f79,plain,(
% 0.39/0.83    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f44,f67])).
% 0.39/0.83  fof(f682,plain,(
% 0.39/0.83    spl4_48 | ~spl4_15),
% 0.39/0.83    inference(avatar_split_clause,[],[f628,f203,f679])).
% 0.39/0.83  fof(f679,plain,(
% 0.39/0.83    spl4_48 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.39/0.83  fof(f628,plain,(
% 0.39/0.83    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_15),
% 0.39/0.83    inference(superposition,[],[f79,f205])).
% 0.39/0.83  fof(f673,plain,(
% 0.39/0.83    spl4_47 | ~spl4_1),
% 0.39/0.83    inference(avatar_split_clause,[],[f363,f70,f670])).
% 0.39/0.83  fof(f670,plain,(
% 0.39/0.83    spl4_47 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.39/0.83  fof(f70,plain,(
% 0.39/0.83    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.39/0.83  fof(f363,plain,(
% 0.39/0.83    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_1),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f72,f52])).
% 0.39/0.83  fof(f72,plain,(
% 0.39/0.83    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.39/0.83    inference(avatar_component_clause,[],[f70])).
% 0.39/0.83  fof(f668,plain,(
% 0.39/0.83    spl4_46 | ~spl4_44),
% 0.39/0.83    inference(avatar_split_clause,[],[f649,f639,f665])).
% 0.39/0.83  fof(f639,plain,(
% 0.39/0.83    spl4_44 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.39/0.83  fof(f649,plain,(
% 0.39/0.83    r1_xboole_0(sK1,k1_xboole_0) | ~spl4_44),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f641,f51])).
% 0.39/0.83  fof(f641,plain,(
% 0.39/0.83    r1_xboole_0(k1_xboole_0,sK1) | ~spl4_44),
% 0.39/0.83    inference(avatar_component_clause,[],[f639])).
% 0.39/0.83  fof(f647,plain,(
% 0.39/0.83    spl4_45 | ~spl4_15),
% 0.39/0.83    inference(avatar_split_clause,[],[f620,f203,f644])).
% 0.39/0.83  fof(f620,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_15),
% 0.39/0.83    inference(superposition,[],[f44,f205])).
% 0.39/0.83  fof(f642,plain,(
% 0.39/0.83    spl4_44 | ~spl4_15),
% 0.39/0.83    inference(avatar_split_clause,[],[f619,f203,f639])).
% 0.39/0.83  fof(f619,plain,(
% 0.39/0.83    r1_xboole_0(k1_xboole_0,sK1) | ~spl4_15),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f205,f55])).
% 0.39/0.83  fof(f617,plain,(
% 0.39/0.83    spl4_43 | ~spl4_12),
% 0.39/0.83    inference(avatar_split_clause,[],[f182,f178,f614])).
% 0.39/0.83  fof(f178,plain,(
% 0.39/0.83    spl4_12 <=> r1_tarski(k1_xboole_0,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.39/0.83  fof(f182,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl4_12),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f180,f61])).
% 0.39/0.83  fof(f180,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK2) | ~spl4_12),
% 0.39/0.83    inference(avatar_component_clause,[],[f178])).
% 0.39/0.83  fof(f610,plain,(
% 0.39/0.83    ~spl4_42 | spl4_21),
% 0.39/0.83    inference(avatar_split_clause,[],[f264,f257,f607])).
% 0.39/0.83  fof(f257,plain,(
% 0.39/0.83    spl4_21 <=> r1_tarski(sK0,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.39/0.83  fof(f264,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK0,sK2) | spl4_21),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f259,f60])).
% 0.39/0.83  fof(f259,plain,(
% 0.39/0.83    ~r1_tarski(sK0,sK2) | spl4_21),
% 0.39/0.83    inference(avatar_component_clause,[],[f257])).
% 0.39/0.83  fof(f577,plain,(
% 0.39/0.83    spl4_41 | ~spl4_40),
% 0.39/0.83    inference(avatar_split_clause,[],[f571,f564,f574])).
% 0.39/0.83  fof(f571,plain,(
% 0.39/0.83    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_40),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f566,f51])).
% 0.39/0.83  fof(f567,plain,(
% 0.39/0.83    spl4_40 | ~spl4_32),
% 0.39/0.83    inference(avatar_split_clause,[],[f498,f410,f564])).
% 0.39/0.83  fof(f498,plain,(
% 0.39/0.83    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_32),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f412,f65])).
% 0.39/0.83  fof(f562,plain,(
% 0.39/0.83    ~spl4_39 | spl4_19),
% 0.39/0.83    inference(avatar_split_clause,[],[f479,f240,f559])).
% 0.39/0.83  fof(f240,plain,(
% 0.39/0.83    spl4_19 <=> r1_tarski(sK1,sK2)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.39/0.83  fof(f479,plain,(
% 0.39/0.83    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl4_19),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f241,f60])).
% 0.39/0.83  fof(f241,plain,(
% 0.39/0.83    ~r1_tarski(sK1,sK2) | spl4_19),
% 0.39/0.83    inference(avatar_component_clause,[],[f240])).
% 0.39/0.83  fof(f528,plain,(
% 0.39/0.83    ~spl4_38 | spl4_37),
% 0.39/0.83    inference(avatar_split_clause,[],[f521,f516,f525])).
% 0.39/0.83  fof(f525,plain,(
% 0.39/0.83    spl4_38 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.39/0.83  fof(f516,plain,(
% 0.39/0.83    spl4_37 <=> r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.39/0.83  fof(f521,plain,(
% 0.39/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_37),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f518,f47])).
% 0.39/0.83  fof(f518,plain,(
% 0.39/0.83    ~r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_37),
% 0.39/0.83    inference(avatar_component_clause,[],[f516])).
% 0.39/0.83  fof(f519,plain,(
% 0.39/0.83    ~spl4_37 | spl4_34),
% 0.39/0.83    inference(avatar_split_clause,[],[f451,f443,f516])).
% 0.39/0.83  fof(f451,plain,(
% 0.39/0.83    ~r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_34),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f445,f68])).
% 0.39/0.83  fof(f512,plain,(
% 0.39/0.83    ~spl4_36 | spl4_35),
% 0.39/0.83    inference(avatar_split_clause,[],[f495,f490,f509])).
% 0.39/0.83  fof(f509,plain,(
% 0.39/0.83    spl4_36 <=> m1_subset_1(sK0,k1_zfmisc_1(sK1))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.39/0.83  fof(f490,plain,(
% 0.39/0.83    spl4_35 <=> r2_hidden(sK0,k1_zfmisc_1(sK1))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.39/0.83  fof(f495,plain,(
% 0.39/0.83    ~m1_subset_1(sK0,k1_zfmisc_1(sK1)) | spl4_35),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f492,f47])).
% 0.39/0.83  fof(f492,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | spl4_35),
% 0.39/0.83    inference(avatar_component_clause,[],[f490])).
% 0.39/0.83  fof(f493,plain,(
% 0.39/0.83    ~spl4_35 | spl4_33),
% 0.39/0.83    inference(avatar_split_clause,[],[f439,f431,f490])).
% 0.39/0.83  fof(f439,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | spl4_33),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f433,f68])).
% 0.39/0.83  fof(f472,plain,(
% 0.39/0.83    ~spl4_1 | ~spl4_2 | ~spl4_19 | spl4_20),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f471])).
% 0.39/0.83  fof(f471,plain,(
% 0.39/0.83    $false | (~spl4_1 | ~spl4_2 | ~spl4_19 | spl4_20)),
% 0.39/0.83    inference(subsumption_resolution,[],[f415,f421])).
% 0.39/0.83  fof(f421,plain,(
% 0.39/0.83    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) ) | ~spl4_19),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f242,f63])).
% 0.39/0.83  fof(f242,plain,(
% 0.39/0.83    r1_tarski(sK1,sK2) | ~spl4_19),
% 0.39/0.83    inference(avatar_component_clause,[],[f240])).
% 0.39/0.83  fof(f415,plain,(
% 0.39/0.83    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_1 | ~spl4_2 | spl4_20)),
% 0.39/0.83    inference(forward_demodulation,[],[f414,f364])).
% 0.39/0.83  fof(f414,plain,(
% 0.39/0.83    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_1 | spl4_20)),
% 0.39/0.83    inference(forward_demodulation,[],[f245,f363])).
% 0.39/0.83  fof(f245,plain,(
% 0.39/0.83    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_20),
% 0.39/0.83    inference(avatar_component_clause,[],[f244])).
% 0.39/0.83  fof(f244,plain,(
% 0.39/0.83    spl4_20 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.39/0.83  fof(f470,plain,(
% 0.39/0.83    ~spl4_19 | spl4_32),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f469])).
% 0.39/0.83  fof(f469,plain,(
% 0.39/0.83    $false | (~spl4_19 | spl4_32)),
% 0.39/0.83    inference(subsumption_resolution,[],[f461,f242])).
% 0.39/0.83  fof(f461,plain,(
% 0.39/0.83    ~r1_tarski(sK1,sK2) | spl4_32),
% 0.39/0.83    inference(resolution,[],[f411,f63])).
% 0.39/0.83  fof(f411,plain,(
% 0.39/0.83    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_32),
% 0.39/0.83    inference(avatar_component_clause,[],[f410])).
% 0.39/0.83  fof(f468,plain,(
% 0.39/0.83    ~spl4_19 | spl4_32),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f467])).
% 0.39/0.83  fof(f467,plain,(
% 0.39/0.83    $false | (~spl4_19 | spl4_32)),
% 0.39/0.83    inference(subsumption_resolution,[],[f454,f242])).
% 0.39/0.83  fof(f454,plain,(
% 0.39/0.83    ~r1_tarski(sK1,sK2) | spl4_32),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f411,f63])).
% 0.39/0.83  fof(f464,plain,(
% 0.39/0.83    ~spl4_19 | spl4_32),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f455])).
% 0.39/0.83  fof(f455,plain,(
% 0.39/0.83    $false | (~spl4_19 | spl4_32)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f242,f411,f63])).
% 0.39/0.83  fof(f446,plain,(
% 0.39/0.83    ~spl4_34 | ~spl4_19 | spl4_22),
% 0.39/0.83    inference(avatar_split_clause,[],[f422,f269,f240,f443])).
% 0.39/0.83  fof(f422,plain,(
% 0.39/0.83    ~r1_tarski(sK2,k1_xboole_0) | (~spl4_19 | spl4_22)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f271,f242,f66])).
% 0.39/0.83  fof(f434,plain,(
% 0.39/0.83    ~spl4_33 | ~spl4_19 | spl4_21),
% 0.39/0.83    inference(avatar_split_clause,[],[f426,f257,f240,f431])).
% 0.39/0.83  fof(f426,plain,(
% 0.39/0.83    ~r1_tarski(sK0,sK1) | (~spl4_19 | spl4_21)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f259,f242,f66])).
% 0.39/0.83  fof(f420,plain,(
% 0.39/0.83    ~spl4_24 | spl4_25),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f419])).
% 0.39/0.83  fof(f419,plain,(
% 0.39/0.83    $false | (~spl4_24 | spl4_25)),
% 0.39/0.83    inference(subsumption_resolution,[],[f297,f418])).
% 0.39/0.83  fof(f418,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | spl4_25),
% 0.39/0.83    inference(subsumption_resolution,[],[f311,f43])).
% 0.39/0.83  fof(f311,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl4_25),
% 0.39/0.83    inference(resolution,[],[f307,f48])).
% 0.39/0.83  fof(f307,plain,(
% 0.39/0.83    ~m1_subset_1(sK1,k1_zfmisc_1(sK2)) | spl4_25),
% 0.39/0.83    inference(avatar_component_clause,[],[f305])).
% 0.39/0.83  fof(f305,plain,(
% 0.39/0.83    spl4_25 <=> m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.39/0.83  fof(f297,plain,(
% 0.39/0.83    r2_hidden(sK1,k1_zfmisc_1(sK2)) | ~spl4_24),
% 0.39/0.83    inference(avatar_component_clause,[],[f296])).
% 0.39/0.83  fof(f296,plain,(
% 0.39/0.83    spl4_24 <=> r2_hidden(sK1,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.39/0.83  fof(f417,plain,(
% 0.39/0.83    ~spl4_19 | spl4_24),
% 0.39/0.83    inference(avatar_contradiction_clause,[],[f416])).
% 0.39/0.83  fof(f416,plain,(
% 0.39/0.83    $false | (~spl4_19 | spl4_24)),
% 0.39/0.83    inference(subsumption_resolution,[],[f242,f302])).
% 0.39/0.83  fof(f302,plain,(
% 0.39/0.83    ~r1_tarski(sK1,sK2) | spl4_24),
% 0.39/0.83    inference(resolution,[],[f298,f67])).
% 0.39/0.83  fof(f298,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | spl4_24),
% 0.39/0.83    inference(avatar_component_clause,[],[f296])).
% 0.39/0.83  fof(f413,plain,(
% 0.39/0.83    spl4_32 | ~spl4_1 | ~spl4_2 | ~spl4_20),
% 0.39/0.83    inference(avatar_split_clause,[],[f376,f244,f75,f70,f410])).
% 0.39/0.83  fof(f376,plain,(
% 0.39/0.83    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_20)),
% 0.39/0.83    inference(backward_demodulation,[],[f374,f363])).
% 0.39/0.83  fof(f374,plain,(
% 0.39/0.83    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | (~spl4_2 | ~spl4_20)),
% 0.39/0.83    inference(backward_demodulation,[],[f246,f364])).
% 0.39/0.83  fof(f246,plain,(
% 0.39/0.83    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_20),
% 0.39/0.83    inference(avatar_component_clause,[],[f244])).
% 0.39/0.83  fof(f394,plain,(
% 0.39/0.83    ~spl4_31 | spl4_29),
% 0.39/0.83    inference(avatar_split_clause,[],[f358,f349,f391])).
% 0.39/0.83  fof(f391,plain,(
% 0.39/0.83    spl4_31 <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.39/0.83  fof(f349,plain,(
% 0.39/0.83    spl4_29 <=> r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.39/0.83  fof(f358,plain,(
% 0.39/0.83    ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | spl4_29),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f351,f47])).
% 0.39/0.83  fof(f351,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0)) | spl4_29),
% 0.39/0.83    inference(avatar_component_clause,[],[f349])).
% 0.39/0.83  fof(f389,plain,(
% 0.39/0.83    ~spl4_30 | spl4_28),
% 0.39/0.83    inference(avatar_split_clause,[],[f354,f344,f386])).
% 0.39/0.83  fof(f386,plain,(
% 0.39/0.83    spl4_30 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.39/0.83  fof(f344,plain,(
% 0.39/0.83    spl4_28 <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.39/0.83  fof(f354,plain,(
% 0.39/0.83    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl4_28),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f346,f47])).
% 0.39/0.83  fof(f346,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl4_28),
% 0.39/0.83    inference(avatar_component_clause,[],[f344])).
% 0.39/0.83  fof(f352,plain,(
% 0.39/0.83    ~spl4_29 | spl4_23),
% 0.39/0.83    inference(avatar_split_clause,[],[f292,f274,f349])).
% 0.39/0.83  fof(f292,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0)) | spl4_23),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f276,f68])).
% 0.39/0.83  fof(f347,plain,(
% 0.39/0.83    ~spl4_28 | spl4_22),
% 0.39/0.83    inference(avatar_split_clause,[],[f286,f269,f344])).
% 0.39/0.83  fof(f286,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl4_22),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f271,f68])).
% 0.39/0.83  fof(f325,plain,(
% 0.39/0.83    ~spl4_27 | spl4_26),
% 0.39/0.83    inference(avatar_split_clause,[],[f318,f313,f322])).
% 0.39/0.83  fof(f322,plain,(
% 0.39/0.83    spl4_27 <=> m1_subset_1(sK0,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.39/0.83  fof(f313,plain,(
% 0.39/0.83    spl4_26 <=> r2_hidden(sK0,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.39/0.83  fof(f318,plain,(
% 0.39/0.83    ~m1_subset_1(sK0,k1_zfmisc_1(sK2)) | spl4_26),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f315,f47])).
% 0.39/0.83  fof(f315,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(sK2)) | spl4_26),
% 0.39/0.83    inference(avatar_component_clause,[],[f313])).
% 0.39/0.83  fof(f316,plain,(
% 0.39/0.83    ~spl4_26 | spl4_21),
% 0.39/0.83    inference(avatar_split_clause,[],[f265,f257,f313])).
% 0.39/0.83  fof(f265,plain,(
% 0.39/0.83    ~r2_hidden(sK0,k1_zfmisc_1(sK2)) | spl4_21),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f259,f68])).
% 0.39/0.83  fof(f309,plain,(
% 0.39/0.83    ~spl4_19 | ~spl4_20),
% 0.39/0.83    inference(avatar_split_clause,[],[f42,f244,f240])).
% 0.39/0.83  fof(f42,plain,(
% 0.39/0.83    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.39/0.83    inference(cnf_transformation,[],[f31])).
% 0.39/0.83  fof(f31,plain,(
% 0.39/0.83    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.39/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).
% 0.39/0.83  fof(f29,plain,(
% 0.39/0.83    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.39/0.83    introduced(choice_axiom,[])).
% 0.39/0.83  fof(f30,plain,(
% 0.39/0.83    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.39/0.83    introduced(choice_axiom,[])).
% 0.39/0.83  fof(f28,plain,(
% 0.39/0.83    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.83    inference(flattening,[],[f27])).
% 0.39/0.83  fof(f27,plain,(
% 0.39/0.83    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.83    inference(nnf_transformation,[],[f18])).
% 0.39/0.83  fof(f18,plain,(
% 0.39/0.83    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.83    inference(ennf_transformation,[],[f17])).
% 0.39/0.83  fof(f17,negated_conjecture,(
% 0.39/0.83    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.39/0.83    inference(negated_conjecture,[],[f16])).
% 0.39/0.83  fof(f16,conjecture,(
% 0.39/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.39/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.39/0.83  fof(f308,plain,(
% 0.39/0.83    ~spl4_25 | spl4_24),
% 0.39/0.83    inference(avatar_split_clause,[],[f301,f296,f305])).
% 0.39/0.83  fof(f301,plain,(
% 0.39/0.83    ~m1_subset_1(sK1,k1_zfmisc_1(sK2)) | spl4_24),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f298,f47])).
% 0.39/0.83  fof(f299,plain,(
% 0.39/0.83    ~spl4_24 | spl4_19),
% 0.39/0.83    inference(avatar_split_clause,[],[f253,f240,f296])).
% 0.39/0.83  fof(f253,plain,(
% 0.39/0.83    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | spl4_19),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f241,f68])).
% 0.39/0.83  fof(f277,plain,(
% 0.39/0.83    ~spl4_23 | ~spl4_12 | spl4_21),
% 0.39/0.83    inference(avatar_split_clause,[],[f262,f257,f178,f274])).
% 0.39/0.83  fof(f262,plain,(
% 0.39/0.83    ~r1_tarski(sK0,k1_xboole_0) | (~spl4_12 | spl4_21)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f180,f259,f66])).
% 0.39/0.83  fof(f272,plain,(
% 0.39/0.83    ~spl4_22 | ~spl4_12 | spl4_19),
% 0.39/0.83    inference(avatar_split_clause,[],[f250,f240,f178,f269])).
% 0.39/0.83  fof(f250,plain,(
% 0.39/0.83    ~r1_tarski(sK1,k1_xboole_0) | (~spl4_12 | spl4_19)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f180,f241,f66])).
% 0.39/0.83  fof(f260,plain,(
% 0.39/0.83    ~spl4_21 | ~spl4_5 | spl4_19),
% 0.39/0.83    inference(avatar_split_clause,[],[f248,f240,f95,f257])).
% 0.39/0.83  fof(f248,plain,(
% 0.39/0.83    ~r1_tarski(sK0,sK2) | (~spl4_5 | spl4_19)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f97,f241,f66])).
% 0.39/0.83  fof(f247,plain,(
% 0.39/0.83    spl4_19 | spl4_20),
% 0.39/0.83    inference(avatar_split_clause,[],[f41,f244,f240])).
% 0.39/0.83  fof(f41,plain,(
% 0.39/0.83    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.39/0.83    inference(cnf_transformation,[],[f31])).
% 0.39/0.83  fof(f238,plain,(
% 0.39/0.83    spl4_18 | ~spl4_17),
% 0.39/0.83    inference(avatar_split_clause,[],[f233,f228,f235])).
% 0.39/0.83  fof(f228,plain,(
% 0.39/0.83    spl4_17 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.39/0.83  fof(f233,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_17),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f230,f48])).
% 0.39/0.83  fof(f230,plain,(
% 0.39/0.83    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_17),
% 0.39/0.83    inference(avatar_component_clause,[],[f228])).
% 0.39/0.83  fof(f231,plain,(
% 0.39/0.83    spl4_17 | ~spl4_16),
% 0.39/0.83    inference(avatar_split_clause,[],[f225,f219,f228])).
% 0.39/0.83  fof(f225,plain,(
% 0.39/0.83    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_16),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f221,f67])).
% 0.39/0.83  fof(f222,plain,(
% 0.39/0.83    spl4_16 | ~spl4_6 | ~spl4_12),
% 0.39/0.83    inference(avatar_split_clause,[],[f213,f178,f105,f219])).
% 0.39/0.83  fof(f105,plain,(
% 0.39/0.83    spl4_6 <=> r1_tarski(sK2,sK0)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.39/0.83  fof(f213,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK0) | (~spl4_6 | ~spl4_12)),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f180,f107,f66])).
% 0.39/0.83  fof(f107,plain,(
% 0.39/0.83    r1_tarski(sK2,sK0) | ~spl4_6),
% 0.39/0.83    inference(avatar_component_clause,[],[f105])).
% 0.39/0.83  fof(f206,plain,(
% 0.39/0.83    spl4_15 | ~spl4_9),
% 0.39/0.83    inference(avatar_split_clause,[],[f149,f145,f203])).
% 0.39/0.83  fof(f145,plain,(
% 0.39/0.83    spl4_9 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.39/0.83  fof(f149,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl4_9),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f147,f61])).
% 0.39/0.83  fof(f147,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK1) | ~spl4_9),
% 0.39/0.83    inference(avatar_component_clause,[],[f145])).
% 0.39/0.83  fof(f198,plain,(
% 0.39/0.83    spl4_14 | ~spl4_8),
% 0.39/0.83    inference(avatar_split_clause,[],[f175,f126,f195])).
% 0.39/0.83  fof(f175,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | ~spl4_8),
% 0.39/0.83    inference(superposition,[],[f100,f128])).
% 0.39/0.83  fof(f193,plain,(
% 0.39/0.83    spl4_13 | ~spl4_8),
% 0.39/0.83    inference(avatar_split_clause,[],[f174,f126,f190])).
% 0.39/0.83  fof(f190,plain,(
% 0.39/0.83    spl4_13 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.39/0.83  fof(f174,plain,(
% 0.39/0.83    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2)) | ~spl4_8),
% 0.39/0.83    inference(superposition,[],[f79,f128])).
% 0.39/0.83  fof(f181,plain,(
% 0.39/0.83    spl4_12 | ~spl4_8),
% 0.39/0.83    inference(avatar_split_clause,[],[f169,f126,f178])).
% 0.39/0.83  fof(f169,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK2) | ~spl4_8),
% 0.39/0.83    inference(superposition,[],[f44,f128])).
% 0.39/0.83  fof(f161,plain,(
% 0.39/0.83    spl4_11 | ~spl4_7),
% 0.39/0.83    inference(avatar_split_clause,[],[f142,f121,f158])).
% 0.39/0.83  fof(f142,plain,(
% 0.39/0.83    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl4_7),
% 0.39/0.83    inference(superposition,[],[f100,f123])).
% 0.39/0.83  fof(f156,plain,(
% 0.39/0.83    spl4_10 | ~spl4_7),
% 0.39/0.83    inference(avatar_split_clause,[],[f141,f121,f153])).
% 0.39/0.83  fof(f153,plain,(
% 0.39/0.83    spl4_10 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.39/0.83  fof(f141,plain,(
% 0.39/0.83    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl4_7),
% 0.39/0.83    inference(superposition,[],[f79,f123])).
% 0.39/0.83  fof(f148,plain,(
% 0.39/0.83    spl4_9 | ~spl4_7),
% 0.39/0.83    inference(avatar_split_clause,[],[f136,f121,f145])).
% 0.39/0.83  fof(f136,plain,(
% 0.39/0.83    r1_tarski(k1_xboole_0,sK1) | ~spl4_7),
% 0.39/0.83    inference(superposition,[],[f44,f123])).
% 0.39/0.83  fof(f129,plain,(
% 0.39/0.83    spl4_8 | ~spl4_6),
% 0.39/0.83    inference(avatar_split_clause,[],[f115,f105,f126])).
% 0.39/0.83  fof(f115,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl4_6),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f107,f61])).
% 0.39/0.83  fof(f124,plain,(
% 0.39/0.83    spl4_7 | ~spl4_5),
% 0.39/0.83    inference(avatar_split_clause,[],[f114,f95,f121])).
% 0.39/0.83  fof(f114,plain,(
% 0.39/0.83    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl4_5),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f97,f61])).
% 0.39/0.83  fof(f108,plain,(
% 0.39/0.83    spl4_6 | ~spl4_4),
% 0.39/0.83    inference(avatar_split_clause,[],[f102,f89,f105])).
% 0.39/0.83  fof(f89,plain,(
% 0.39/0.83    spl4_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.39/0.83  fof(f102,plain,(
% 0.39/0.83    r1_tarski(sK2,sK0) | ~spl4_4),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f91,f68])).
% 0.39/0.83  fof(f91,plain,(
% 0.39/0.83    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.39/0.83    inference(avatar_component_clause,[],[f89])).
% 0.39/0.83  fof(f98,plain,(
% 0.39/0.83    spl4_5 | ~spl4_3),
% 0.39/0.83    inference(avatar_split_clause,[],[f93,f84,f95])).
% 0.39/0.83  fof(f84,plain,(
% 0.39/0.83    spl4_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.39/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.39/0.83  fof(f93,plain,(
% 0.39/0.83    r1_tarski(sK1,sK0) | ~spl4_3),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f86,f68])).
% 0.39/0.83  fof(f86,plain,(
% 0.39/0.83    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.39/0.83    inference(avatar_component_clause,[],[f84])).
% 0.39/0.83  fof(f92,plain,(
% 0.39/0.83    spl4_4 | ~spl4_2),
% 0.39/0.83    inference(avatar_split_clause,[],[f82,f75,f89])).
% 0.39/0.83  fof(f82,plain,(
% 0.39/0.83    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f77,f47])).
% 0.39/0.83  fof(f87,plain,(
% 0.39/0.83    spl4_3 | ~spl4_1),
% 0.39/0.83    inference(avatar_split_clause,[],[f81,f70,f84])).
% 0.39/0.83  fof(f81,plain,(
% 0.39/0.83    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.39/0.83    inference(unit_resulting_resolution,[],[f43,f72,f47])).
% 0.39/0.83  fof(f78,plain,(
% 0.39/0.83    spl4_2),
% 0.39/0.83    inference(avatar_split_clause,[],[f40,f75])).
% 0.39/0.83  fof(f40,plain,(
% 0.39/0.83    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.39/0.83    inference(cnf_transformation,[],[f31])).
% 0.39/0.83  fof(f73,plain,(
% 0.39/0.83    spl4_1),
% 0.39/0.83    inference(avatar_split_clause,[],[f39,f70])).
% 0.39/0.83  fof(f39,plain,(
% 0.39/0.83    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.39/0.83    inference(cnf_transformation,[],[f31])).
% 0.39/0.83  % SZS output end Proof for theBenchmark
% 0.39/0.83  % (23517)------------------------------
% 0.39/0.83  % (23517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.83  % (23517)Termination reason: Refutation
% 0.39/0.83  
% 0.39/0.83  % (23517)Memory used [KB]: 4477
% 0.39/0.83  % (23517)Time elapsed: 0.242 s
% 0.39/0.83  % (23517)------------------------------
% 0.39/0.83  % (23517)------------------------------
% 0.39/0.83  % (23282)Success in time 0.471 s
%------------------------------------------------------------------------------
