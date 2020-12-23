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
% DateTime   : Thu Dec  3 12:52:30 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  313 ( 683 expanded)
%              Number of leaves         :   75 ( 331 expanded)
%              Depth                    :   11
%              Number of atoms          :  905 (1728 expanded)
%              Number of equality atoms :  189 ( 437 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1023,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f98,f103,f107,f115,f121,f125,f136,f140,f144,f153,f161,f168,f172,f189,f193,f211,f220,f242,f246,f270,f319,f323,f359,f368,f389,f399,f421,f455,f459,f479,f528,f565,f583,f592,f608,f627,f638,f646,f701,f734,f783,f801,f805,f831,f844,f858,f924,f937,f966,f1019])).

fof(f1019,plain,
    ( ~ spl2_14
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_40
    | ~ spl2_64
    | spl2_67
    | ~ spl2_74
    | ~ spl2_76 ),
    inference(avatar_contradiction_clause,[],[f1011])).

fof(f1011,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_40
    | ~ spl2_64
    | spl2_67
    | ~ spl2_74
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f800,f1010])).

fof(f1010,plain,
    ( ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_14
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_40
    | ~ spl2_64
    | ~ spl2_74
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1009,f215])).

fof(f215,plain,
    ( ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_14
    | ~ spl2_21 ),
    inference(resolution,[],[f210,f152])).

fof(f152,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_14
  <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_21
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f1009,plain,
    ( ! [X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_28
    | ~ spl2_40
    | ~ spl2_64
    | ~ spl2_74
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f997,f943])).

fof(f943,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_28
    | ~ spl2_40
    | ~ spl2_64
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f938,f756])).

fof(f756,plain,
    ( ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X5),X6))
    | ~ spl2_40
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f740,f388])).

fof(f388,plain,
    ( ! [X6,X5] : k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl2_40
  <=> ! [X5,X6] : k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f740,plain,
    ( ! [X6,X5] : k7_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X5),X6)) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))
    | ~ spl2_40
    | ~ spl2_64 ),
    inference(superposition,[],[f388,f733])).

fof(f733,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl2_64
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f938,plain,
    ( ! [X0,X1] : k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_28
    | ~ spl2_74 ),
    inference(resolution,[],[f936,f269])).

fof(f269,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(X5,X6)
        | k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl2_28
  <=> ! [X5,X6] :
        ( k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5)
        | ~ r1_tarski(X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f936,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f935])).

fof(f935,plain,
    ( spl2_74
  <=> ! [X1,X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f997,plain,
    ( ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X4)),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_28
    | ~ spl2_76 ),
    inference(resolution,[],[f965,f269])).

fof(f965,plain,
    ( ! [X39,X40] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f964])).

fof(f964,plain,
    ( spl2_76
  <=> ! [X40,X39] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f800,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_67 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl2_67
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f966,plain,
    ( spl2_76
    | ~ spl2_68
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f878,f856,f803,f964])).

fof(f803,plain,
    ( spl2_68
  <=> ! [X5,X6] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f856,plain,
    ( spl2_71
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f878,plain,
    ( ! [X39,X40] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40))
    | ~ spl2_68
    | ~ spl2_71 ),
    inference(superposition,[],[f804,f857])).

fof(f857,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f856])).

fof(f804,plain,
    ( ! [X6,X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f803])).

fof(f937,plain,
    ( spl2_74
    | ~ spl2_58
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f933,f922,f636,f935])).

fof(f636,plain,
    ( spl2_58
  <=> ! [X5,X6] : k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f922,plain,
    ( spl2_73
  <=> ! [X22,X23,X24] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f933,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)
    | ~ spl2_58
    | ~ spl2_73 ),
    inference(superposition,[],[f923,f637])).

fof(f637,plain,
    ( ! [X6,X5] : k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f636])).

fof(f923,plain,
    ( ! [X24,X23,X22] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22)
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f922])).

fof(f924,plain,
    ( spl2_73
    | ~ spl2_53
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f871,f856,f581,f922])).

fof(f581,plain,
    ( spl2_53
  <=> ! [X1,X0,X2] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f871,plain,
    ( ! [X24,X23,X22] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22)
    | ~ spl2_53
    | ~ spl2_71 ),
    inference(superposition,[],[f582,f857])).

fof(f582,plain,
    ( ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f581])).

fof(f858,plain,
    ( spl2_71
    | ~ spl2_40
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f849,f842,f387,f856])).

fof(f842,plain,
    ( spl2_70
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f849,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_40
    | ~ spl2_70 ),
    inference(superposition,[],[f843,f388])).

fof(f843,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f842])).

fof(f844,plain,
    ( spl2_70
    | ~ spl2_59
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f836,f829,f644,f842])).

fof(f644,plain,
    ( spl2_59
  <=> ! [X9,X7,X8] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f829,plain,
    ( spl2_69
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f836,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_59
    | ~ spl2_69 ),
    inference(superposition,[],[f645,f830])).

fof(f830,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f829])).

fof(f645,plain,
    ( ! [X8,X7,X9] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f644])).

fof(f831,plain,
    ( spl2_69
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f793,f781,f170,f151,f829])).

fof(f170,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f781,plain,
    ( spl2_66
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f793,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_66 ),
    inference(subsumption_resolution,[],[f785,f152])).

fof(f785,plain,
    ( ! [X2,X3] :
        ( k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) )
    | ~ spl2_17
    | ~ spl2_66 ),
    inference(resolution,[],[f782,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f782,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f781])).

fof(f805,plain,
    ( spl2_68
    | ~ spl2_64
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f791,f781,f732,f803])).

fof(f791,plain,
    ( ! [X6,X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6))
    | ~ spl2_64
    | ~ spl2_66 ),
    inference(superposition,[],[f782,f733])).

fof(f801,plain,
    ( ~ spl2_67
    | ~ spl2_1
    | ~ spl2_2
    | spl2_33
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f773,f590,f316,f84,f80,f798])).

fof(f80,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f316,plain,
    ( spl2_33
  <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f590,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f773,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_33
    | ~ spl2_54 ),
    inference(backward_demodulation,[],[f318,f772])).

fof(f772,plain,
    ( ! [X6,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k1_setfam_1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f769,f85])).

fof(f85,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f769,plain,
    ( ! [X6,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),X6))
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(resolution,[],[f591,f81])).

fof(f81,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f590])).

fof(f318,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_33 ),
    inference(avatar_component_clause,[],[f316])).

fof(f783,plain,
    ( spl2_66
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_26
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f776,f590,f244,f84,f80,f781])).

fof(f244,plain,
    ( spl2_26
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f776,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_26
    | ~ spl2_54 ),
    inference(backward_demodulation,[],[f245,f772])).

fof(f245,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f734,plain,
    ( spl2_64
    | ~ spl2_34
    | ~ spl2_56
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f723,f699,f606,f321,f732])).

fof(f321,plain,
    ( spl2_34
  <=> ! [X5,X6] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f606,plain,
    ( spl2_56
  <=> ! [X9,X7,X8] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f699,plain,
    ( spl2_62
  <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f723,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)
    | ~ spl2_34
    | ~ spl2_56
    | ~ spl2_62 ),
    inference(forward_demodulation,[],[f712,f322])).

fof(f322,plain,
    ( ! [X6,X5] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f321])).

fof(f712,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3)
    | ~ spl2_56
    | ~ spl2_62 ),
    inference(superposition,[],[f700,f607])).

fof(f607,plain,
    ( ! [X8,X7,X9] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f606])).

fof(f700,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)))
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f699])).

fof(f701,plain,
    ( spl2_62
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f157,f151,f138,f105,f699])).

fof(f105,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f138,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f157,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)))
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f156,f139])).

fof(f139,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f156,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(resolution,[],[f152,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f646,plain,
    ( spl2_59
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_39
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f541,f526,f366,f151,f134,f119,f96,f80,f644])).

fof(f96,plain,
    ( spl2_5
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f119,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f134,plain,
    ( spl2_11
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f366,plain,
    ( spl2_39
  <=> ! [X5,X6] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f526,plain,
    ( spl2_51
  <=> ! [X9,X7,X8] :
        ( ~ v1_relat_1(X7)
        | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f541,plain,
    ( ! [X8,X7,X9] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_39
    | ~ spl2_51 ),
    inference(backward_demodulation,[],[f384,f540])).

fof(f540,plain,
    ( ! [X8,X7,X9] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8)
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f537,f135])).

fof(f135,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f537,plain,
    ( ! [X8,X7,X9] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X9)),X8)
    | ~ spl2_1
    | ~ spl2_51 ),
    inference(resolution,[],[f527,f81])).

fof(f527,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_relat_1(X7)
        | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9) )
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f526])).

fof(f384,plain,
    ( ! [X8,X7,X9] : k5_relat_1(k7_relat_1(k6_relat_1(X9),X8),k6_relat_1(X7)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f383,f155])).

fof(f155,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(resolution,[],[f152,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f383,plain,
    ( ! [X8,X7,X9] : k4_relat_1(k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9))) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X8),k6_relat_1(X7))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f372,f375])).

fof(f375,plain,
    ( ! [X6,X5] : k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f374,f135])).

fof(f374,plain,
    ( ! [X6,X5] : k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f373,f135])).

fof(f373,plain,
    ( ! [X6,X5] : k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k4_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f371,f97])).

fof(f97,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f371,plain,
    ( ! [X6,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k4_relat_1(k6_relat_1(X6)),k6_relat_1(X5))
    | ~ spl2_1
    | ~ spl2_39 ),
    inference(resolution,[],[f367,f81])).

fof(f367,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(X5)
        | k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6)) )
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f366])).

fof(f372,plain,
    ( ! [X8,X7,X9] : k4_relat_1(k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X8),X9)),k6_relat_1(X7))
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(resolution,[],[f367,f152])).

fof(f638,plain,
    ( spl2_58
    | ~ spl2_12
    | ~ spl2_46
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f634,f625,f453,f138,f636])).

fof(f453,plain,
    ( spl2_46
  <=> ! [X1,X0,X2] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f625,plain,
    ( spl2_57
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f634,plain,
    ( ! [X6,X5] : k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)
    | ~ spl2_12
    | ~ spl2_46
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f633,f139])).

fof(f633,plain,
    ( ! [X6,X5] : k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)
    | ~ spl2_46
    | ~ spl2_57 ),
    inference(superposition,[],[f454,f626])).

fof(f626,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f625])).

fof(f454,plain,
    ( ! [X2,X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f453])).

fof(f627,plain,
    ( spl2_57
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f615,f606,f159,f134,f625])).

fof(f159,plain,
    ( spl2_15
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f615,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f609,f135])).

fof(f609,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_15
    | ~ spl2_56 ),
    inference(superposition,[],[f607,f160])).

fof(f160,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f608,plain,
    ( spl2_56
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f540,f526,f134,f80,f606])).

fof(f592,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f78,f590])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f583,plain,
    ( spl2_53
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f574,f563,f166,f159,f581])).

fof(f166,plain,
    ( spl2_16
  <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f563,plain,
    ( spl2_52
  <=> ! [X11,X13,X10,X12] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f574,plain,
    ( ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_52 ),
    inference(forward_demodulation,[],[f568,f167])).

fof(f167,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f568,plain,
    ( ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X0),X0))
    | ~ spl2_15
    | ~ spl2_52 ),
    inference(superposition,[],[f564,f160])).

fof(f564,plain,
    ( ! [X12,X10,X13,X11] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f563])).

fof(f565,plain,
    ( spl2_52
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_41
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f560,f526,f477,f457,f397,f151,f123,f563])).

fof(f123,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f397,plain,
    ( spl2_41
  <=> ! [X3,X2,X4] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f457,plain,
    ( spl2_47
  <=> ! [X3,X5,X4] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f477,plain,
    ( spl2_48
  <=> ! [X3,X5,X4] : v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f560,plain,
    ( ! [X12,X10,X13,X11] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13))
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_41
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f559,f482])).

fof(f482,plain,
    ( ! [X10,X8,X7,X9] : k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X9),X10)) = k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X9),X10)
    | ~ spl2_10
    | ~ spl2_48 ),
    inference(resolution,[],[f478,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f478,plain,
    ( ! [X4,X5,X3] : v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f477])).

fof(f559,plain,
    ( ! [X12,X10,X13,X11] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11)),k9_relat_1(k6_relat_1(X12),X13))
    | ~ spl2_14
    | ~ spl2_41
    | ~ spl2_47
    | ~ spl2_51 ),
    inference(backward_demodulation,[],[f411,f558])).

fof(f558,plain,
    ( ! [X12,X10,X13,X11] : k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11)
    | ~ spl2_14
    | ~ spl2_47
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f538,f458])).

fof(f458,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f457])).

fof(f538,plain,
    ( ! [X12,X10,X13,X11] : k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k5_relat_1(k6_relat_1(X10),k7_relat_1(k6_relat_1(X12),X13)),X11)
    | ~ spl2_14
    | ~ spl2_51 ),
    inference(resolution,[],[f527,f152])).

fof(f411,plain,
    ( ! [X12,X10,X13,X11] : r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13))),k9_relat_1(k6_relat_1(X12),X13))
    | ~ spl2_14
    | ~ spl2_41 ),
    inference(resolution,[],[f398,f152])).

fof(f398,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X4)
        | r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f397])).

fof(f528,plain,
    ( spl2_51
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f518,f419,f80,f526])).

fof(f419,plain,
    ( spl2_45
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f518,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_relat_1(X7)
        | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9) )
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(resolution,[],[f420,f81])).

fof(f420,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f419])).

fof(f479,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f474,f457,f151,f101,f80,f477])).

fof(f101,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f474,plain,
    ( ! [X4,X5,X3] : v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f473,f81])).

fof(f473,plain,
    ( ! [X4,X5,X3] :
        ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f468,f152])).

fof(f468,plain,
    ( ! [X4,X5,X3] :
        ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X4),X5))
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_6
    | ~ spl2_47 ),
    inference(superposition,[],[f102,f458])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f459,plain,
    ( spl2_47
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f155,f151,f119,f457])).

fof(f455,plain,
    ( spl2_46
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f154,f151,f123,f453])).

fof(f154,plain,
    ( ! [X2,X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(resolution,[],[f152,f124])).

fof(f421,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f63,f419])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f399,plain,
    ( spl2_41
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f185,f151,f142,f138,f397])).

fof(f142,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f185,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))
        | ~ v1_relat_1(X4) )
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f176,f152])).

fof(f176,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
        | ~ v1_relat_1(X4) )
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(superposition,[],[f143,f139])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f389,plain,
    ( spl2_40
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f375,f366,f134,f96,f80,f387])).

fof(f368,plain,
    ( spl2_39
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f364,f357,f96,f80,f366])).

fof(f357,plain,
    ( spl2_38
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f364,plain,
    ( ! [X6,X5] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6))
        | ~ v1_relat_1(X5) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f362,f97])).

fof(f362,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(X5)
        | k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k4_relat_1(k6_relat_1(X6))) )
    | ~ spl2_1
    | ~ spl2_38 ),
    inference(resolution,[],[f358,f81])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,(
    spl2_38 ),
    inference(avatar_split_clause,[],[f53,f357])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f323,plain,
    ( spl2_34
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f228,f218,f191,f321])).

fof(f191,plain,
    ( spl2_19
  <=> ! [X1,X2] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f218,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f228,plain,
    ( ! [X6,X5] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)
    | ~ spl2_19
    | ~ spl2_22 ),
    inference(resolution,[],[f219,f192])).

fof(f192,plain,
    ( ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f319,plain,
    ( ~ spl2_33
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f129,f119,f80,f316])).

fof(f129,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f76,f126])).

fof(f126,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(resolution,[],[f120,f81])).

fof(f76,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43])).

fof(f43,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f270,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f265,f240,f134,f88,f80,f268])).

fof(f88,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f240,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f265,plain,
    ( ! [X6,X5] :
        ( k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5)
        | ~ r1_tarski(X5,X6) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f264,f135])).

fof(f264,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(X5,X6)
        | k6_relat_1(X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f262,f89])).

fof(f89,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f262,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X5)),X6)
        | k6_relat_1(X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)) )
    | ~ spl2_1
    | ~ spl2_25 ),
    inference(resolution,[],[f241,f81])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f246,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f77,f244])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f242,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f62,f240])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f220,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f207,f170,f84,f80,f218])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f206,f81])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(superposition,[],[f171,f85])).

fof(f211,plain,
    ( spl2_21
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f205,f187,f170,f209])).

fof(f187,plain,
    ( spl2_18
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f205,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(resolution,[],[f171,f188])).

fof(f188,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f193,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f183,f142,f138,f134,f88,f80,f191])).

fof(f183,plain,
    ( ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f182,f139])).

fof(f182,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f181,f89])).

fof(f181,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f180,f81])).

fof(f180,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f174,f81])).

fof(f174,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(superposition,[],[f143,f135])).

fof(f189,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f179,f142,f113,f88,f80,f187])).

fof(f113,plain,
    ( spl2_8
  <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f179,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f178,f89])).

fof(f178,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f177,f81])).

fof(f177,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(superposition,[],[f143,f114])).

fof(f114,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f172,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f60,f170])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f168,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f164,f159,f138,f88,f166])).

fof(f164,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f163,f89])).

fof(f163,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(superposition,[],[f139,f160])).

fof(f161,plain,
    ( spl2_15
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f145,f134,f113,f159])).

fof(f145,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(superposition,[],[f135,f114])).

fof(f153,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f149,f134,f101,f80,f151])).

fof(f149,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f148,f81])).

fof(f148,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f147,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f102,f135])).

fof(f144,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f52,f142])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f140,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f130,f123,f80,f138])).

fof(f130,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f124,f81])).

fof(f136,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f126,f119,f80,f134])).

fof(f125,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f121,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f57,f119])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f115,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f111,f105,f88,f80,f113])).

fof(f111,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f108,f89])).

fof(f108,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f106,f81])).

fof(f107,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f103,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f64,f101])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f98,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f90,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f86,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (27346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (27335)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (27334)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (27336)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (27343)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (27348)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (27332)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (27333)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (27338)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (27347)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (27345)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (27341)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (27331)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (27342)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (27340)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (27342)Refutation not found, incomplete strategy% (27342)------------------------------
% 0.21/0.50  % (27342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27342)Memory used [KB]: 10618
% 0.21/0.50  % (27342)Time elapsed: 0.052 s
% 0.21/0.50  % (27342)------------------------------
% 0.21/0.50  % (27342)------------------------------
% 0.21/0.50  % (27344)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (27337)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (27339)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.24/0.52  % (27338)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f1023,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f82,f86,f90,f98,f103,f107,f115,f121,f125,f136,f140,f144,f153,f161,f168,f172,f189,f193,f211,f220,f242,f246,f270,f319,f323,f359,f368,f389,f399,f421,f455,f459,f479,f528,f565,f583,f592,f608,f627,f638,f646,f701,f734,f783,f801,f805,f831,f844,f858,f924,f937,f966,f1019])).
% 1.37/0.54  fof(f1019,plain,(
% 1.37/0.54    ~spl2_14 | ~spl2_21 | ~spl2_28 | ~spl2_40 | ~spl2_64 | spl2_67 | ~spl2_74 | ~spl2_76),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f1011])).
% 1.37/0.54  fof(f1011,plain,(
% 1.37/0.54    $false | (~spl2_14 | ~spl2_21 | ~spl2_28 | ~spl2_40 | ~spl2_64 | spl2_67 | ~spl2_74 | ~spl2_76)),
% 1.37/0.54    inference(subsumption_resolution,[],[f800,f1010])).
% 1.37/0.54  fof(f1010,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | (~spl2_14 | ~spl2_21 | ~spl2_28 | ~spl2_40 | ~spl2_64 | ~spl2_74 | ~spl2_76)),
% 1.37/0.54    inference(forward_demodulation,[],[f1009,f215])).
% 1.37/0.54  fof(f215,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | (~spl2_14 | ~spl2_21)),
% 1.37/0.54    inference(resolution,[],[f210,f152])).
% 1.37/0.54  fof(f152,plain,(
% 1.37/0.54    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_14),
% 1.37/0.54    inference(avatar_component_clause,[],[f151])).
% 1.37/0.54  fof(f151,plain,(
% 1.37/0.54    spl2_14 <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.37/0.54  fof(f210,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_21),
% 1.37/0.54    inference(avatar_component_clause,[],[f209])).
% 1.37/0.54  fof(f209,plain,(
% 1.37/0.54    spl2_21 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.37/0.54  fof(f1009,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | (~spl2_28 | ~spl2_40 | ~spl2_64 | ~spl2_74 | ~spl2_76)),
% 1.37/0.54    inference(forward_demodulation,[],[f997,f943])).
% 1.37/0.54  fof(f943,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_28 | ~spl2_40 | ~spl2_64 | ~spl2_74)),
% 1.37/0.54    inference(forward_demodulation,[],[f938,f756])).
% 1.37/0.54  fof(f756,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X5),X6))) ) | (~spl2_40 | ~spl2_64)),
% 1.37/0.54    inference(forward_demodulation,[],[f740,f388])).
% 1.37/0.54  fof(f388,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | ~spl2_40),
% 1.37/0.54    inference(avatar_component_clause,[],[f387])).
% 1.37/0.54  fof(f387,plain,(
% 1.37/0.54    spl2_40 <=> ! [X5,X6] : k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 1.37/0.54  fof(f740,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),k9_relat_1(k6_relat_1(X5),X6)) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ) | (~spl2_40 | ~spl2_64)),
% 1.37/0.54    inference(superposition,[],[f388,f733])).
% 1.37/0.54  fof(f733,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) ) | ~spl2_64),
% 1.37/0.54    inference(avatar_component_clause,[],[f732])).
% 1.37/0.54  fof(f732,plain,(
% 1.37/0.54    spl2_64 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 1.37/0.54  fof(f938,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_28 | ~spl2_74)),
% 1.37/0.54    inference(resolution,[],[f936,f269])).
% 1.37/0.54  fof(f269,plain,(
% 1.37/0.54    ( ! [X6,X5] : (~r1_tarski(X5,X6) | k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5)) ) | ~spl2_28),
% 1.37/0.54    inference(avatar_component_clause,[],[f268])).
% 1.37/0.54  fof(f268,plain,(
% 1.37/0.54    spl2_28 <=> ! [X5,X6] : (k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,X6))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.37/0.54  fof(f936,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)) ) | ~spl2_74),
% 1.37/0.54    inference(avatar_component_clause,[],[f935])).
% 1.37/0.54  fof(f935,plain,(
% 1.37/0.54    spl2_74 <=> ! [X1,X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 1.37/0.54  fof(f997,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X4)),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | (~spl2_28 | ~spl2_76)),
% 1.37/0.54    inference(resolution,[],[f965,f269])).
% 1.37/0.54  fof(f965,plain,(
% 1.37/0.54    ( ! [X39,X40] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40))) ) | ~spl2_76),
% 1.37/0.54    inference(avatar_component_clause,[],[f964])).
% 1.37/0.54  fof(f964,plain,(
% 1.37/0.54    spl2_76 <=> ! [X40,X39] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.37/0.54  fof(f800,plain,(
% 1.37/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_67),
% 1.37/0.54    inference(avatar_component_clause,[],[f798])).
% 1.37/0.54  fof(f798,plain,(
% 1.37/0.54    spl2_67 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 1.37/0.54  fof(f966,plain,(
% 1.37/0.54    spl2_76 | ~spl2_68 | ~spl2_71),
% 1.37/0.54    inference(avatar_split_clause,[],[f878,f856,f803,f964])).
% 1.37/0.54  fof(f803,plain,(
% 1.37/0.54    spl2_68 <=> ! [X5,X6] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 1.37/0.54  fof(f856,plain,(
% 1.37/0.54    spl2_71 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 1.37/0.54  fof(f878,plain,(
% 1.37/0.54    ( ! [X39,X40] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X40),X39)),k9_relat_1(k6_relat_1(X39),X40))) ) | (~spl2_68 | ~spl2_71)),
% 1.37/0.54    inference(superposition,[],[f804,f857])).
% 1.37/0.54  fof(f857,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | ~spl2_71),
% 1.37/0.54    inference(avatar_component_clause,[],[f856])).
% 1.37/0.54  fof(f804,plain,(
% 1.37/0.54    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6))) ) | ~spl2_68),
% 1.37/0.54    inference(avatar_component_clause,[],[f803])).
% 1.37/0.54  fof(f937,plain,(
% 1.37/0.54    spl2_74 | ~spl2_58 | ~spl2_73),
% 1.37/0.54    inference(avatar_split_clause,[],[f933,f922,f636,f935])).
% 1.37/0.54  fof(f636,plain,(
% 1.37/0.54    spl2_58 <=> ! [X5,X6] : k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 1.37/0.54  fof(f922,plain,(
% 1.37/0.54    spl2_73 <=> ! [X22,X23,X24] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 1.37/0.54  fof(f933,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)) ) | (~spl2_58 | ~spl2_73)),
% 1.37/0.54    inference(superposition,[],[f923,f637])).
% 1.37/0.54  fof(f637,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)) ) | ~spl2_58),
% 1.37/0.54    inference(avatar_component_clause,[],[f636])).
% 1.37/0.54  fof(f923,plain,(
% 1.37/0.54    ( ! [X24,X23,X22] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22)) ) | ~spl2_73),
% 1.37/0.54    inference(avatar_component_clause,[],[f922])).
% 1.37/0.54  fof(f924,plain,(
% 1.37/0.54    spl2_73 | ~spl2_53 | ~spl2_71),
% 1.37/0.54    inference(avatar_split_clause,[],[f871,f856,f581,f922])).
% 1.37/0.54  fof(f581,plain,(
% 1.37/0.54    spl2_53 <=> ! [X1,X0,X2] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 1.37/0.54  fof(f871,plain,(
% 1.37/0.54    ( ! [X24,X23,X22] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X23),X22),X24),X22)) ) | (~spl2_53 | ~spl2_71)),
% 1.37/0.54    inference(superposition,[],[f582,f857])).
% 1.37/0.54  fof(f582,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)) ) | ~spl2_53),
% 1.37/0.54    inference(avatar_component_clause,[],[f581])).
% 1.37/0.54  fof(f858,plain,(
% 1.37/0.54    spl2_71 | ~spl2_40 | ~spl2_70),
% 1.37/0.54    inference(avatar_split_clause,[],[f849,f842,f387,f856])).
% 1.37/0.54  fof(f842,plain,(
% 1.37/0.54    spl2_70 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 1.37/0.54  fof(f849,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | (~spl2_40 | ~spl2_70)),
% 1.37/0.54    inference(superposition,[],[f843,f388])).
% 1.37/0.54  fof(f843,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_70),
% 1.37/0.54    inference(avatar_component_clause,[],[f842])).
% 1.37/0.54  fof(f844,plain,(
% 1.37/0.54    spl2_70 | ~spl2_59 | ~spl2_69),
% 1.37/0.54    inference(avatar_split_clause,[],[f836,f829,f644,f842])).
% 1.37/0.54  fof(f644,plain,(
% 1.37/0.54    spl2_59 <=> ! [X9,X7,X8] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 1.37/0.54  fof(f829,plain,(
% 1.37/0.54    spl2_69 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 1.37/0.54  fof(f836,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_59 | ~spl2_69)),
% 1.37/0.54    inference(superposition,[],[f645,f830])).
% 1.37/0.54  fof(f830,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) ) | ~spl2_69),
% 1.37/0.54    inference(avatar_component_clause,[],[f829])).
% 1.37/0.54  fof(f645,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8)) ) | ~spl2_59),
% 1.37/0.54    inference(avatar_component_clause,[],[f644])).
% 1.37/0.54  fof(f831,plain,(
% 1.37/0.54    spl2_69 | ~spl2_14 | ~spl2_17 | ~spl2_66),
% 1.37/0.54    inference(avatar_split_clause,[],[f793,f781,f170,f151,f829])).
% 1.37/0.54  fof(f170,plain,(
% 1.37/0.54    spl2_17 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.37/0.54  fof(f781,plain,(
% 1.37/0.54    spl2_66 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 1.37/0.54  fof(f793,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) ) | (~spl2_14 | ~spl2_17 | ~spl2_66)),
% 1.37/0.54    inference(subsumption_resolution,[],[f785,f152])).
% 1.37/0.54  fof(f785,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_17 | ~spl2_66)),
% 1.37/0.54    inference(resolution,[],[f782,f171])).
% 1.37/0.54  fof(f171,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_17),
% 1.37/0.54    inference(avatar_component_clause,[],[f170])).
% 1.37/0.54  fof(f782,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_66),
% 1.37/0.54    inference(avatar_component_clause,[],[f781])).
% 1.37/0.54  fof(f805,plain,(
% 1.37/0.54    spl2_68 | ~spl2_64 | ~spl2_66),
% 1.37/0.54    inference(avatar_split_clause,[],[f791,f781,f732,f803])).
% 1.37/0.54  fof(f791,plain,(
% 1.37/0.54    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k9_relat_1(k6_relat_1(X5),X6))) ) | (~spl2_64 | ~spl2_66)),
% 1.37/0.54    inference(superposition,[],[f782,f733])).
% 1.37/0.54  fof(f801,plain,(
% 1.37/0.54    ~spl2_67 | ~spl2_1 | ~spl2_2 | spl2_33 | ~spl2_54),
% 1.37/0.54    inference(avatar_split_clause,[],[f773,f590,f316,f84,f80,f798])).
% 1.37/0.54  fof(f80,plain,(
% 1.37/0.54    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.37/0.54  fof(f84,plain,(
% 1.37/0.54    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.37/0.54  fof(f316,plain,(
% 1.37/0.54    spl2_33 <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.37/0.54  fof(f590,plain,(
% 1.37/0.54    spl2_54 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.37/0.54  fof(f773,plain,(
% 1.37/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_33 | ~spl2_54)),
% 1.37/0.54    inference(backward_demodulation,[],[f318,f772])).
% 1.37/0.54  fof(f772,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k1_setfam_1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) ) | (~spl2_1 | ~spl2_2 | ~spl2_54)),
% 1.37/0.54    inference(forward_demodulation,[],[f769,f85])).
% 1.37/0.54  fof(f85,plain,(
% 1.37/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 1.37/0.54    inference(avatar_component_clause,[],[f84])).
% 1.37/0.54  fof(f769,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),k1_relat_1(k6_relat_1(X5)),X6))) ) | (~spl2_1 | ~spl2_54)),
% 1.37/0.54    inference(resolution,[],[f591,f81])).
% 1.37/0.54  fof(f81,plain,(
% 1.37/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 1.37/0.54    inference(avatar_component_clause,[],[f80])).
% 1.37/0.54  fof(f591,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_54),
% 1.37/0.54    inference(avatar_component_clause,[],[f590])).
% 1.37/0.54  fof(f318,plain,(
% 1.37/0.54    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_33),
% 1.37/0.54    inference(avatar_component_clause,[],[f316])).
% 1.37/0.54  fof(f783,plain,(
% 1.37/0.54    spl2_66 | ~spl2_1 | ~spl2_2 | ~spl2_26 | ~spl2_54),
% 1.37/0.54    inference(avatar_split_clause,[],[f776,f590,f244,f84,f80,f781])).
% 1.37/0.54  fof(f244,plain,(
% 1.37/0.54    spl2_26 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.37/0.54  fof(f776,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_26 | ~spl2_54)),
% 1.37/0.54    inference(backward_demodulation,[],[f245,f772])).
% 1.37/0.54  fof(f245,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl2_26),
% 1.37/0.54    inference(avatar_component_clause,[],[f244])).
% 1.37/0.54  fof(f734,plain,(
% 1.37/0.54    spl2_64 | ~spl2_34 | ~spl2_56 | ~spl2_62),
% 1.37/0.54    inference(avatar_split_clause,[],[f723,f699,f606,f321,f732])).
% 1.37/0.54  fof(f321,plain,(
% 1.37/0.54    spl2_34 <=> ! [X5,X6] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.37/0.54  fof(f606,plain,(
% 1.37/0.54    spl2_56 <=> ! [X9,X7,X8] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 1.37/0.54  fof(f699,plain,(
% 1.37/0.54    spl2_62 <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 1.37/0.54  fof(f723,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) ) | (~spl2_34 | ~spl2_56 | ~spl2_62)),
% 1.37/0.54    inference(forward_demodulation,[],[f712,f322])).
% 1.37/0.54  fof(f322,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)) ) | ~spl2_34),
% 1.37/0.54    inference(avatar_component_clause,[],[f321])).
% 1.37/0.54  fof(f712,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3)) ) | (~spl2_56 | ~spl2_62)),
% 1.37/0.54    inference(superposition,[],[f700,f607])).
% 1.37/0.54  fof(f607,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8)) ) | ~spl2_56),
% 1.37/0.54    inference(avatar_component_clause,[],[f606])).
% 1.37/0.54  fof(f700,plain,(
% 1.37/0.54    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)))) ) | ~spl2_62),
% 1.37/0.54    inference(avatar_component_clause,[],[f699])).
% 1.37/0.54  fof(f701,plain,(
% 1.37/0.54    spl2_62 | ~spl2_7 | ~spl2_12 | ~spl2_14),
% 1.37/0.54    inference(avatar_split_clause,[],[f157,f151,f138,f105,f699])).
% 1.37/0.54  fof(f105,plain,(
% 1.37/0.54    spl2_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.37/0.54  fof(f138,plain,(
% 1.37/0.54    spl2_12 <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.37/0.54  fof(f157,plain,(
% 1.37/0.54    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)))) ) | (~spl2_7 | ~spl2_12 | ~spl2_14)),
% 1.37/0.54    inference(forward_demodulation,[],[f156,f139])).
% 1.37/0.54  fof(f139,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_12),
% 1.37/0.54    inference(avatar_component_clause,[],[f138])).
% 1.37/0.54  fof(f156,plain,(
% 1.37/0.54    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))))) ) | (~spl2_7 | ~spl2_14)),
% 1.37/0.54    inference(resolution,[],[f152,f106])).
% 1.37/0.54  fof(f106,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_7),
% 1.37/0.54    inference(avatar_component_clause,[],[f105])).
% 1.37/0.54  fof(f646,plain,(
% 1.37/0.54    spl2_59 | ~spl2_1 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_39 | ~spl2_51),
% 1.37/0.54    inference(avatar_split_clause,[],[f541,f526,f366,f151,f134,f119,f96,f80,f644])).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    spl2_5 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.37/0.54  fof(f119,plain,(
% 1.37/0.54    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.37/0.54  fof(f134,plain,(
% 1.37/0.54    spl2_11 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.37/0.54  fof(f366,plain,(
% 1.37/0.54    spl2_39 <=> ! [X5,X6] : (k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6)) | ~v1_relat_1(X5))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 1.37/0.54  fof(f526,plain,(
% 1.37/0.54    spl2_51 <=> ! [X9,X7,X8] : (~v1_relat_1(X7) | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 1.37/0.54  fof(f541,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),X9),X8)) ) | (~spl2_1 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_39 | ~spl2_51)),
% 1.37/0.54    inference(backward_demodulation,[],[f384,f540])).
% 1.37/0.54  fof(f540,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X7),X8)) ) | (~spl2_1 | ~spl2_11 | ~spl2_51)),
% 1.37/0.54    inference(forward_demodulation,[],[f537,f135])).
% 1.37/0.54  fof(f135,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_11),
% 1.37/0.54    inference(avatar_component_clause,[],[f134])).
% 1.37/0.54  fof(f537,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X9)) = k7_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X9)),X8)) ) | (~spl2_1 | ~spl2_51)),
% 1.37/0.54    inference(resolution,[],[f527,f81])).
% 1.37/0.54  fof(f527,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (~v1_relat_1(X7) | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9)) ) | ~spl2_51),
% 1.37/0.54    inference(avatar_component_clause,[],[f526])).
% 1.37/0.54  fof(f384,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k5_relat_1(k7_relat_1(k6_relat_1(X9),X8),k6_relat_1(X7)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7))) ) | (~spl2_1 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_39)),
% 1.37/0.54    inference(forward_demodulation,[],[f383,f155])).
% 1.37/0.54  fof(f155,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_9 | ~spl2_14)),
% 1.37/0.54    inference(resolution,[],[f152,f120])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 1.37/0.54    inference(avatar_component_clause,[],[f119])).
% 1.37/0.54  fof(f383,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k4_relat_1(k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9))) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X8),k6_relat_1(X7))) ) | (~spl2_1 | ~spl2_5 | ~spl2_11 | ~spl2_14 | ~spl2_39)),
% 1.37/0.54    inference(forward_demodulation,[],[f372,f375])).
% 1.37/0.54  fof(f375,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),X6) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_5 | ~spl2_11 | ~spl2_39)),
% 1.37/0.54    inference(forward_demodulation,[],[f374,f135])).
% 1.37/0.54  fof(f374,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_5 | ~spl2_11 | ~spl2_39)),
% 1.37/0.54    inference(forward_demodulation,[],[f373,f135])).
% 1.37/0.54  fof(f373,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k4_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_5 | ~spl2_39)),
% 1.37/0.54    inference(forward_demodulation,[],[f371,f97])).
% 1.37/0.54  fof(f97,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 1.37/0.54    inference(avatar_component_clause,[],[f96])).
% 1.37/0.54  fof(f371,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k4_relat_1(k6_relat_1(X6)),k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_39)),
% 1.37/0.54    inference(resolution,[],[f367,f81])).
% 1.37/0.54  fof(f367,plain,(
% 1.37/0.54    ( ! [X6,X5] : (~v1_relat_1(X5) | k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6))) ) | ~spl2_39),
% 1.37/0.54    inference(avatar_component_clause,[],[f366])).
% 1.37/0.54  fof(f372,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (k4_relat_1(k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X8),X9)),k6_relat_1(X7))) ) | (~spl2_14 | ~spl2_39)),
% 1.37/0.54    inference(resolution,[],[f367,f152])).
% 1.37/0.54  fof(f638,plain,(
% 1.37/0.54    spl2_58 | ~spl2_12 | ~spl2_46 | ~spl2_57),
% 1.37/0.54    inference(avatar_split_clause,[],[f634,f625,f453,f138,f636])).
% 1.37/0.54  fof(f453,plain,(
% 1.37/0.54    spl2_46 <=> ! [X1,X0,X2] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.37/0.54  fof(f625,plain,(
% 1.37/0.54    spl2_57 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 1.37/0.54  fof(f634,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k9_relat_1(k6_relat_1(X5),X6) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)) ) | (~spl2_12 | ~spl2_46 | ~spl2_57)),
% 1.37/0.54    inference(forward_demodulation,[],[f633,f139])).
% 1.37/0.54  fof(f633,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k9_relat_1(k7_relat_1(k6_relat_1(X5),X6),X6)) ) | (~spl2_46 | ~spl2_57)),
% 1.37/0.54    inference(superposition,[],[f454,f626])).
% 1.37/0.54  fof(f626,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | ~spl2_57),
% 1.37/0.54    inference(avatar_component_clause,[],[f625])).
% 1.37/0.54  fof(f454,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ) | ~spl2_46),
% 1.37/0.54    inference(avatar_component_clause,[],[f453])).
% 1.37/0.54  fof(f627,plain,(
% 1.37/0.54    spl2_57 | ~spl2_11 | ~spl2_15 | ~spl2_56),
% 1.37/0.54    inference(avatar_split_clause,[],[f615,f606,f159,f134,f625])).
% 1.37/0.54  fof(f159,plain,(
% 1.37/0.54    spl2_15 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.37/0.54  fof(f615,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_11 | ~spl2_15 | ~spl2_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f609,f135])).
% 1.37/0.54  fof(f609,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_15 | ~spl2_56)),
% 1.37/0.54    inference(superposition,[],[f607,f160])).
% 1.37/0.54  fof(f160,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_15),
% 1.37/0.54    inference(avatar_component_clause,[],[f159])).
% 1.37/0.54  fof(f608,plain,(
% 1.37/0.54    spl2_56 | ~spl2_1 | ~spl2_11 | ~spl2_51),
% 1.37/0.54    inference(avatar_split_clause,[],[f540,f526,f134,f80,f606])).
% 1.37/0.54  fof(f592,plain,(
% 1.37/0.54    spl2_54),
% 1.37/0.54    inference(avatar_split_clause,[],[f78,f590])).
% 1.37/0.54  fof(f78,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f59,f75])).
% 1.37/0.54  fof(f75,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f55,f74])).
% 1.37/0.54  fof(f74,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f56,f73])).
% 1.37/0.54  fof(f73,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f65,f72])).
% 1.37/0.54  fof(f72,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f66,f71])).
% 1.37/0.54  fof(f71,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f67,f70])).
% 1.37/0.54  fof(f70,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f68,f69])).
% 1.37/0.54  fof(f69,plain,(
% 1.37/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.37/0.54  fof(f67,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.37/0.54  fof(f66,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.37/0.54  fof(f65,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.37/0.54  fof(f59,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f21])).
% 1.37/0.54  fof(f21,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.37/0.54  fof(f583,plain,(
% 1.37/0.54    spl2_53 | ~spl2_15 | ~spl2_16 | ~spl2_52),
% 1.37/0.54    inference(avatar_split_clause,[],[f574,f563,f166,f159,f581])).
% 1.37/0.54  fof(f166,plain,(
% 1.37/0.54    spl2_16 <=> ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.37/0.54  fof(f563,plain,(
% 1.37/0.54    spl2_52 <=> ! [X11,X13,X10,X12] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 1.37/0.54  fof(f574,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)) ) | (~spl2_15 | ~spl2_16 | ~spl2_52)),
% 1.37/0.54    inference(forward_demodulation,[],[f568,f167])).
% 1.37/0.54  fof(f167,plain,(
% 1.37/0.54    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | ~spl2_16),
% 1.37/0.54    inference(avatar_component_clause,[],[f166])).
% 1.37/0.54  fof(f568,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X0),X0))) ) | (~spl2_15 | ~spl2_52)),
% 1.37/0.54    inference(superposition,[],[f564,f160])).
% 1.37/0.54  fof(f564,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13))) ) | ~spl2_52),
% 1.37/0.54    inference(avatar_component_clause,[],[f563])).
% 1.37/0.54  fof(f565,plain,(
% 1.37/0.54    spl2_52 | ~spl2_10 | ~spl2_14 | ~spl2_41 | ~spl2_47 | ~spl2_48 | ~spl2_51),
% 1.37/0.54    inference(avatar_split_clause,[],[f560,f526,f477,f457,f397,f151,f123,f563])).
% 1.37/0.54  fof(f123,plain,(
% 1.37/0.54    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.37/0.54  fof(f397,plain,(
% 1.37/0.54    spl2_41 <=> ! [X3,X2,X4] : (r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X4))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.37/0.54  fof(f457,plain,(
% 1.37/0.54    spl2_47 <=> ! [X3,X5,X4] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 1.37/0.54  fof(f477,plain,(
% 1.37/0.54    spl2_48 <=> ! [X3,X5,X4] : v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 1.37/0.54  fof(f560,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11),k9_relat_1(k6_relat_1(X12),X13))) ) | (~spl2_10 | ~spl2_14 | ~spl2_41 | ~spl2_47 | ~spl2_48 | ~spl2_51)),
% 1.37/0.54    inference(forward_demodulation,[],[f559,f482])).
% 1.37/0.54  fof(f482,plain,(
% 1.37/0.54    ( ! [X10,X8,X7,X9] : (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X9),X10)) = k9_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X8),X9),X10)) ) | (~spl2_10 | ~spl2_48)),
% 1.37/0.54    inference(resolution,[],[f478,f124])).
% 1.37/0.54  fof(f124,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 1.37/0.54    inference(avatar_component_clause,[],[f123])).
% 1.37/0.54  fof(f478,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))) ) | ~spl2_48),
% 1.37/0.54    inference(avatar_component_clause,[],[f477])).
% 1.37/0.54  fof(f559,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11)),k9_relat_1(k6_relat_1(X12),X13))) ) | (~spl2_14 | ~spl2_41 | ~spl2_47 | ~spl2_51)),
% 1.37/0.54    inference(backward_demodulation,[],[f411,f558])).
% 1.37/0.54  fof(f558,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X10),X11)) ) | (~spl2_14 | ~spl2_47 | ~spl2_51)),
% 1.37/0.54    inference(forward_demodulation,[],[f538,f458])).
% 1.37/0.54  fof(f458,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_47),
% 1.37/0.54    inference(avatar_component_clause,[],[f457])).
% 1.37/0.54  fof(f538,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k5_relat_1(k6_relat_1(X10),k7_relat_1(k6_relat_1(X12),X13)),X11)) ) | (~spl2_14 | ~spl2_51)),
% 1.37/0.54    inference(resolution,[],[f527,f152])).
% 1.37/0.54  fof(f411,plain,(
% 1.37/0.54    ( ! [X12,X10,X13,X11] : (r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X10),X11),k7_relat_1(k6_relat_1(X12),X13))),k9_relat_1(k6_relat_1(X12),X13))) ) | (~spl2_14 | ~spl2_41)),
% 1.37/0.54    inference(resolution,[],[f398,f152])).
% 1.37/0.54  fof(f398,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (~v1_relat_1(X4) | r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))) ) | ~spl2_41),
% 1.37/0.54    inference(avatar_component_clause,[],[f397])).
% 1.37/0.54  fof(f528,plain,(
% 1.37/0.54    spl2_51 | ~spl2_1 | ~spl2_45),
% 1.37/0.54    inference(avatar_split_clause,[],[f518,f419,f80,f526])).
% 1.37/0.54  fof(f419,plain,(
% 1.37/0.54    spl2_45 <=> ! [X1,X0,X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.37/0.54  fof(f518,plain,(
% 1.37/0.54    ( ! [X8,X7,X9] : (~v1_relat_1(X7) | k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) = k7_relat_1(k5_relat_1(k6_relat_1(X8),X7),X9)) ) | (~spl2_1 | ~spl2_45)),
% 1.37/0.54    inference(resolution,[],[f420,f81])).
% 1.37/0.54  fof(f420,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) ) | ~spl2_45),
% 1.37/0.54    inference(avatar_component_clause,[],[f419])).
% 1.37/0.54  fof(f479,plain,(
% 1.37/0.54    spl2_48 | ~spl2_1 | ~spl2_6 | ~spl2_14 | ~spl2_47),
% 1.37/0.54    inference(avatar_split_clause,[],[f474,f457,f151,f101,f80,f477])).
% 1.37/0.54  fof(f101,plain,(
% 1.37/0.54    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.37/0.54  fof(f474,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3))) ) | (~spl2_1 | ~spl2_6 | ~spl2_14 | ~spl2_47)),
% 1.37/0.54    inference(subsumption_resolution,[],[f473,f81])).
% 1.37/0.54  fof(f473,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3)) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_6 | ~spl2_14 | ~spl2_47)),
% 1.37/0.54    inference(subsumption_resolution,[],[f468,f152])).
% 1.37/0.54  fof(f468,plain,(
% 1.37/0.54    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),X3)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_6 | ~spl2_47)),
% 1.37/0.54    inference(superposition,[],[f102,f458])).
% 1.37/0.54  fof(f102,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 1.37/0.54    inference(avatar_component_clause,[],[f101])).
% 1.37/0.54  fof(f459,plain,(
% 1.37/0.54    spl2_47 | ~spl2_9 | ~spl2_14),
% 1.37/0.54    inference(avatar_split_clause,[],[f155,f151,f119,f457])).
% 1.37/0.54  fof(f455,plain,(
% 1.37/0.54    spl2_46 | ~spl2_10 | ~spl2_14),
% 1.37/0.54    inference(avatar_split_clause,[],[f154,f151,f123,f453])).
% 1.37/0.54  fof(f154,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ) | (~spl2_10 | ~spl2_14)),
% 1.37/0.54    inference(resolution,[],[f152,f124])).
% 1.37/0.54  fof(f421,plain,(
% 1.37/0.54    spl2_45),
% 1.37/0.54    inference(avatar_split_clause,[],[f63,f419])).
% 1.37/0.54  fof(f63,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f40])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 1.37/0.54  fof(f399,plain,(
% 1.37/0.54    spl2_41 | ~spl2_12 | ~spl2_13 | ~spl2_14),
% 1.37/0.54    inference(avatar_split_clause,[],[f185,f151,f142,f138,f397])).
% 1.37/0.54  fof(f142,plain,(
% 1.37/0.54    spl2_13 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.37/0.54  fof(f185,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X4)) ) | (~spl2_12 | ~spl2_13 | ~spl2_14)),
% 1.37/0.54    inference(subsumption_resolution,[],[f176,f152])).
% 1.37/0.54  fof(f176,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X4)) ) | (~spl2_12 | ~spl2_13)),
% 1.37/0.54    inference(superposition,[],[f143,f139])).
% 1.37/0.54  fof(f143,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 1.37/0.54    inference(avatar_component_clause,[],[f142])).
% 1.37/0.54  fof(f389,plain,(
% 1.37/0.54    spl2_40 | ~spl2_1 | ~spl2_5 | ~spl2_11 | ~spl2_39),
% 1.37/0.54    inference(avatar_split_clause,[],[f375,f366,f134,f96,f80,f387])).
% 1.37/0.54  fof(f368,plain,(
% 1.37/0.54    spl2_39 | ~spl2_1 | ~spl2_5 | ~spl2_38),
% 1.37/0.54    inference(avatar_split_clause,[],[f364,f357,f96,f80,f366])).
% 1.37/0.54  fof(f357,plain,(
% 1.37/0.54    spl2_38 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.37/0.54  fof(f364,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k6_relat_1(X6)) | ~v1_relat_1(X5)) ) | (~spl2_1 | ~spl2_5 | ~spl2_38)),
% 1.37/0.54    inference(forward_demodulation,[],[f362,f97])).
% 1.37/0.54  fof(f362,plain,(
% 1.37/0.54    ( ! [X6,X5] : (~v1_relat_1(X5) | k4_relat_1(k5_relat_1(k6_relat_1(X6),X5)) = k5_relat_1(k4_relat_1(X5),k4_relat_1(k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_38)),
% 1.37/0.54    inference(resolution,[],[f358,f81])).
% 1.37/0.54  fof(f358,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_38),
% 1.37/0.54    inference(avatar_component_clause,[],[f357])).
% 1.37/0.54  fof(f359,plain,(
% 1.37/0.54    spl2_38),
% 1.37/0.54    inference(avatar_split_clause,[],[f53,f357])).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,axiom,(
% 1.37/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.37/0.54  fof(f323,plain,(
% 1.37/0.54    spl2_34 | ~spl2_19 | ~spl2_22),
% 1.37/0.54    inference(avatar_split_clause,[],[f228,f218,f191,f321])).
% 1.37/0.54  fof(f191,plain,(
% 1.37/0.54    spl2_19 <=> ! [X1,X2] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.37/0.54  fof(f218,plain,(
% 1.37/0.54    spl2_22 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.37/0.54  fof(f228,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)) ) | (~spl2_19 | ~spl2_22)),
% 1.37/0.54    inference(resolution,[],[f219,f192])).
% 1.37/0.54  fof(f192,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)) ) | ~spl2_19),
% 1.37/0.54    inference(avatar_component_clause,[],[f191])).
% 1.37/0.54  fof(f219,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_22),
% 1.37/0.54    inference(avatar_component_clause,[],[f218])).
% 1.37/0.54  fof(f319,plain,(
% 1.37/0.54    ~spl2_33 | ~spl2_1 | ~spl2_9),
% 1.37/0.54    inference(avatar_split_clause,[],[f129,f119,f80,f316])).
% 1.37/0.54  fof(f129,plain,(
% 1.37/0.54    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_9)),
% 1.37/0.54    inference(backward_demodulation,[],[f76,f126])).
% 1.37/0.54  fof(f126,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_9)),
% 1.37/0.54    inference(resolution,[],[f120,f81])).
% 1.37/0.54  fof(f76,plain,(
% 1.37/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.37/0.54    inference(definition_unfolding,[],[f45,f75])).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f25])).
% 1.37/0.54  fof(f25,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.37/0.54    inference(negated_conjecture,[],[f24])).
% 1.37/0.54  fof(f24,conjecture,(
% 1.37/0.54    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.37/0.54  fof(f270,plain,(
% 1.37/0.54    spl2_28 | ~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_25),
% 1.37/0.54    inference(avatar_split_clause,[],[f265,f240,f134,f88,f80,f268])).
% 1.37/0.54  fof(f88,plain,(
% 1.37/0.54    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.37/0.54  fof(f240,plain,(
% 1.37/0.54    spl2_25 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 1.37/0.54  fof(f265,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k6_relat_1(X5) = k7_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,X6)) ) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_25)),
% 1.37/0.54    inference(forward_demodulation,[],[f264,f135])).
% 1.37/0.54  fof(f264,plain,(
% 1.37/0.54    ( ! [X6,X5] : (~r1_tarski(X5,X6) | k6_relat_1(X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) ) | (~spl2_1 | ~spl2_3 | ~spl2_25)),
% 1.37/0.54    inference(forward_demodulation,[],[f262,f89])).
% 1.37/0.54  fof(f89,plain,(
% 1.37/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 1.37/0.54    inference(avatar_component_clause,[],[f88])).
% 1.37/0.54  fof(f262,plain,(
% 1.37/0.54    ( ! [X6,X5] : (~r1_tarski(k2_relat_1(k6_relat_1(X5)),X6) | k6_relat_1(X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) ) | (~spl2_1 | ~spl2_25)),
% 1.37/0.54    inference(resolution,[],[f241,f81])).
% 1.37/0.54  fof(f241,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_25),
% 1.37/0.54    inference(avatar_component_clause,[],[f240])).
% 1.37/0.54  fof(f246,plain,(
% 1.37/0.54    spl2_26),
% 1.37/0.54    inference(avatar_split_clause,[],[f77,f244])).
% 1.37/0.54  fof(f77,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f54,f75])).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.37/0.54  fof(f242,plain,(
% 1.37/0.54    spl2_25),
% 1.37/0.54    inference(avatar_split_clause,[],[f62,f240])).
% 1.37/0.54  fof(f62,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(flattening,[],[f38])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f19])).
% 1.37/0.54  fof(f19,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.37/0.54  fof(f220,plain,(
% 1.37/0.54    spl2_22 | ~spl2_1 | ~spl2_2 | ~spl2_17),
% 1.37/0.54    inference(avatar_split_clause,[],[f207,f170,f84,f80,f218])).
% 1.37/0.54  fof(f207,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_17)),
% 1.37/0.54    inference(subsumption_resolution,[],[f206,f81])).
% 1.37/0.54  fof(f206,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_17)),
% 1.37/0.54    inference(superposition,[],[f171,f85])).
% 1.37/0.54  fof(f211,plain,(
% 1.37/0.54    spl2_21 | ~spl2_17 | ~spl2_18),
% 1.37/0.54    inference(avatar_split_clause,[],[f205,f187,f170,f209])).
% 1.37/0.54  fof(f187,plain,(
% 1.37/0.54    spl2_18 <=> ! [X0] : r1_tarski(X0,X0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.37/0.54  fof(f205,plain,(
% 1.37/0.54    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | (~spl2_17 | ~spl2_18)),
% 1.37/0.54    inference(resolution,[],[f171,f188])).
% 1.37/0.54  fof(f188,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_18),
% 1.37/0.54    inference(avatar_component_clause,[],[f187])).
% 1.37/0.54  fof(f193,plain,(
% 1.37/0.54    spl2_19 | ~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_12 | ~spl2_13),
% 1.37/0.54    inference(avatar_split_clause,[],[f183,f142,f138,f134,f88,f80,f191])).
% 1.37/0.54  fof(f183,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)) ) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_12 | ~spl2_13)),
% 1.37/0.54    inference(forward_demodulation,[],[f182,f139])).
% 1.37/0.54  fof(f182,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) ) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_13)),
% 1.37/0.54    inference(forward_demodulation,[],[f181,f89])).
% 1.37/0.54  fof(f181,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_11 | ~spl2_13)),
% 1.37/0.54    inference(subsumption_resolution,[],[f180,f81])).
% 1.37/0.54  fof(f180,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_11 | ~spl2_13)),
% 1.37/0.54    inference(subsumption_resolution,[],[f174,f81])).
% 1.37/0.54  fof(f174,plain,(
% 1.37/0.54    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_11 | ~spl2_13)),
% 1.37/0.54    inference(superposition,[],[f143,f135])).
% 1.37/0.54  fof(f189,plain,(
% 1.37/0.54    spl2_18 | ~spl2_1 | ~spl2_3 | ~spl2_8 | ~spl2_13),
% 1.37/0.54    inference(avatar_split_clause,[],[f179,f142,f113,f88,f80,f187])).
% 1.37/0.54  fof(f113,plain,(
% 1.37/0.54    spl2_8 <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.37/0.54  fof(f179,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_8 | ~spl2_13)),
% 1.37/0.54    inference(forward_demodulation,[],[f178,f89])).
% 1.37/0.54  fof(f178,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_8 | ~spl2_13)),
% 1.37/0.54    inference(subsumption_resolution,[],[f177,f81])).
% 1.37/0.54  fof(f177,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_8 | ~spl2_13)),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f173])).
% 1.37/0.54  fof(f173,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_8 | ~spl2_13)),
% 1.37/0.54    inference(superposition,[],[f143,f114])).
% 1.37/0.54  fof(f114,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl2_8),
% 1.37/0.54    inference(avatar_component_clause,[],[f113])).
% 1.37/0.54  fof(f172,plain,(
% 1.37/0.54    spl2_17),
% 1.37/0.54    inference(avatar_split_clause,[],[f60,f170])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(flattening,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f23])).
% 1.37/0.54  fof(f23,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.37/0.54  fof(f168,plain,(
% 1.37/0.54    spl2_16 | ~spl2_3 | ~spl2_12 | ~spl2_15),
% 1.37/0.54    inference(avatar_split_clause,[],[f164,f159,f138,f88,f166])).
% 1.37/0.54  fof(f164,plain,(
% 1.37/0.54    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) ) | (~spl2_3 | ~spl2_12 | ~spl2_15)),
% 1.37/0.54    inference(forward_demodulation,[],[f163,f89])).
% 1.37/0.54  fof(f163,plain,(
% 1.37/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_12 | ~spl2_15)),
% 1.37/0.54    inference(superposition,[],[f139,f160])).
% 1.37/0.54  fof(f161,plain,(
% 1.37/0.54    spl2_15 | ~spl2_8 | ~spl2_11),
% 1.37/0.54    inference(avatar_split_clause,[],[f145,f134,f113,f159])).
% 1.37/0.54  fof(f145,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_8 | ~spl2_11)),
% 1.37/0.54    inference(superposition,[],[f135,f114])).
% 1.37/0.54  fof(f153,plain,(
% 1.37/0.54    spl2_14 | ~spl2_1 | ~spl2_6 | ~spl2_11),
% 1.37/0.54    inference(avatar_split_clause,[],[f149,f134,f101,f80,f151])).
% 1.37/0.54  fof(f149,plain,(
% 1.37/0.54    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_6 | ~spl2_11)),
% 1.37/0.54    inference(subsumption_resolution,[],[f148,f81])).
% 1.37/0.54  fof(f148,plain,(
% 1.37/0.54    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_6 | ~spl2_11)),
% 1.37/0.54    inference(subsumption_resolution,[],[f147,f81])).
% 1.37/0.54  fof(f147,plain,(
% 1.37/0.54    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_6 | ~spl2_11)),
% 1.37/0.54    inference(superposition,[],[f102,f135])).
% 1.37/0.54  fof(f144,plain,(
% 1.37/0.54    spl2_13),
% 1.37/0.54    inference(avatar_split_clause,[],[f52,f142])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,axiom,(
% 1.37/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.37/0.54  fof(f140,plain,(
% 1.37/0.54    spl2_12 | ~spl2_1 | ~spl2_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f130,f123,f80,f138])).
% 1.37/0.54  fof(f130,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_10)),
% 1.37/0.54    inference(resolution,[],[f124,f81])).
% 1.37/0.54  fof(f136,plain,(
% 1.37/0.54    spl2_11 | ~spl2_1 | ~spl2_9),
% 1.37/0.54    inference(avatar_split_clause,[],[f126,f119,f80,f134])).
% 1.37/0.54  fof(f125,plain,(
% 1.37/0.54    spl2_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f58,f123])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.37/0.54  fof(f121,plain,(
% 1.37/0.54    spl2_9),
% 1.37/0.54    inference(avatar_split_clause,[],[f57,f119])).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f22])).
% 1.37/0.54  fof(f22,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.37/0.54  fof(f115,plain,(
% 1.37/0.54    spl2_8 | ~spl2_1 | ~spl2_3 | ~spl2_7),
% 1.37/0.54    inference(avatar_split_clause,[],[f111,f105,f88,f80,f113])).
% 1.37/0.54  fof(f111,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_7)),
% 1.37/0.54    inference(forward_demodulation,[],[f108,f89])).
% 1.37/0.54  fof(f108,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) ) | (~spl2_1 | ~spl2_7)),
% 1.37/0.54    inference(resolution,[],[f106,f81])).
% 1.37/0.54  fof(f107,plain,(
% 1.37/0.54    spl2_7),
% 1.37/0.54    inference(avatar_split_clause,[],[f51,f105])).
% 1.37/0.54  fof(f51,plain,(
% 1.37/0.54    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f20])).
% 1.37/0.54  fof(f20,axiom,(
% 1.37/0.54    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.37/0.54  fof(f103,plain,(
% 1.37/0.54    spl2_6),
% 1.37/0.54    inference(avatar_split_clause,[],[f64,f101])).
% 1.37/0.54  fof(f64,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(flattening,[],[f41])).
% 1.37/0.54  fof(f41,plain,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f10])).
% 1.37/0.54  fof(f10,axiom,(
% 1.37/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.37/0.54  fof(f98,plain,(
% 1.37/0.54    spl2_5),
% 1.37/0.54    inference(avatar_split_clause,[],[f47,f96])).
% 1.37/0.54  fof(f47,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,axiom,(
% 1.37/0.54    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.37/0.54  fof(f90,plain,(
% 1.37/0.54    spl2_3),
% 1.37/0.54    inference(avatar_split_clause,[],[f49,f88])).
% 1.37/0.54  fof(f49,plain,(
% 1.37/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,axiom,(
% 1.37/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.37/0.54  fof(f86,plain,(
% 1.37/0.54    spl2_2),
% 1.37/0.54    inference(avatar_split_clause,[],[f48,f84])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f82,plain,(
% 1.37/0.54    spl2_1),
% 1.37/0.54    inference(avatar_split_clause,[],[f46,f80])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,axiom,(
% 1.37/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (27338)------------------------------
% 1.37/0.54  % (27338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (27338)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (27338)Memory used [KB]: 6908
% 1.37/0.54  % (27338)Time elapsed: 0.095 s
% 1.37/0.54  % (27338)------------------------------
% 1.37/0.54  % (27338)------------------------------
% 1.37/0.54  % (27330)Success in time 0.183 s
%------------------------------------------------------------------------------
