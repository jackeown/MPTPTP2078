%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:12 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 273 expanded)
%              Number of leaves         :   37 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 ( 690 expanded)
%              Number of equality atoms :  102 ( 207 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f42,f50,f54,f58,f78,f91,f95,f136,f175,f196,f205,f226,f280,f473,f479,f491,f666,f671,f789,f1245,f1347,f1513,f1800,f2321,f2382])).

fof(f2382,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | spl3_52
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_81 ),
    inference(avatar_contradiction_clause,[],[f2381])).

fof(f2381,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | spl3_52
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1244,f2380])).

fof(f2380,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k4_xboole_0(X36,X37))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_68
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2379,f1803])).

fof(f1803,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_68 ),
    inference(unit_resulting_resolution,[],[f36,f1799])).

fof(f1799,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1798,plain,
    ( spl3_68
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f36,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2379,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k3_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X36,X37)))
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2378,f279])).

fof(f279,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_24
  <=> ! [X3,X4] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f2378,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(X36,X37)))
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2377,f1525])).

fof(f1525,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl3_9
    | ~ spl3_60 ),
    inference(superposition,[],[f77,f1512])).

fof(f1512,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f1511])).

fof(f1511,plain,
    ( spl3_60
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f77,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2377,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(X36,X37))))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2376,f714])).

fof(f714,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f681,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f681,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_14
    | ~ spl3_40 ),
    inference(unit_resulting_resolution,[],[f135,f670])).

fof(f670,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4)
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl3_40
  <=> ! [X3,X2,X4] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f135,plain,
    ( ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_14
  <=> ! [X5,X4] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2376,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(k3_xboole_0(X35,X36),X37)))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2375,f1348])).

fof(f1348,plain,
    ( ! [X12,X13,X11] : k3_xboole_0(X12,k4_xboole_0(X11,X13)) = k3_xboole_0(X11,k4_xboole_0(X12,X13))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_40
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f715,f1346])).

fof(f1346,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1345,plain,
    ( spl3_56
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f715,plain,
    ( ! [X12,X13,X11] :
        ( k3_xboole_0(X12,k4_xboole_0(X11,X13)) = k3_xboole_0(X11,k4_xboole_0(X12,X13))
        | ~ r1_tarski(k3_xboole_0(X11,X12),X12) )
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f693,f714])).

fof(f693,plain,
    ( ! [X12,X13,X11] :
        ( k4_xboole_0(k3_xboole_0(X11,X12),X13) = k3_xboole_0(X12,k4_xboole_0(X11,X13))
        | ~ r1_tarski(k3_xboole_0(X11,X12),X12) )
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(superposition,[],[f670,f490])).

fof(f490,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl3_34
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f2375,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37)))
    | ~ spl3_43
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f2354,f788])).

fof(f788,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl3_43
  <=> ! [X5,X7,X6] : k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f2354,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(X35,k3_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X37))) = k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X37))
    | ~ spl3_43
    | ~ spl3_81 ),
    inference(superposition,[],[f788,f2320])).

fof(f2320,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f2319,plain,
    ( spl3_81
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f1244,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f1242])).

fof(f1242,plain,
    ( spl3_52
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f2321,plain,
    ( spl3_81
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f680,f669,f52,f2319])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f680,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(unit_resulting_resolution,[],[f53,f670])).

fof(f53,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f1800,plain,
    ( spl3_68
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f230,f224,f40,f1798])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f224,plain,
    ( spl3_22
  <=> ! [X1,X2] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f230,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(superposition,[],[f225,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f225,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f224])).

fof(f1513,plain,
    ( spl3_60
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f228,f224,f52,f1511])).

fof(f228,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f53,f225])).

fof(f1347,plain,
    ( spl3_56
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f138,f134,f40,f1345])).

fof(f138,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(superposition,[],[f135,f41])).

fof(f1245,plain,
    ( ~ spl3_52
    | spl3_1
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f807,f787,f26,f1242])).

fof(f26,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f807,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_1
    | ~ spl3_43 ),
    inference(superposition,[],[f28,f788])).

fof(f28,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f789,plain,
    ( spl3_43
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f127,f93,f56,f787])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f127,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f94,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f94,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f671,plain,
    ( spl3_40
    | ~ spl3_19
    | ~ spl3_33
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f667,f664,f477,f173,f669])).

fof(f173,plain,
    ( spl3_19
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f477,plain,
    ( spl3_33
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f664,plain,
    ( spl3_39
  <=> ! [X3,X2,X4] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4))
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f667,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4)
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_19
    | ~ spl3_33
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f665,f486])).

fof(f486,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,X11) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X10,X11))
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(superposition,[],[f478,f174])).

fof(f174,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f478,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f477])).

fof(f665,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4))
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f664])).

fof(f666,plain,
    ( spl3_39
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f122,f93,f48,f664])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f122,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4))
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f94,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f491,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f105,f89,f40,f489])).

fof(f105,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f90,f41])).

fof(f479,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_21
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f475,f471,f203,f31,f477])).

fof(f31,plain,
    ( spl3_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f203,plain,
    ( spl3_21
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f471,plain,
    ( spl3_32
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f475,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl3_2
    | ~ spl3_21
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f474,f32])).

fof(f32,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f474,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_21
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f472,f204])).

fof(f204,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f472,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f471])).

fof(f473,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f125,f93,f31,f471])).

fof(f125,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(superposition,[],[f94,f32])).

fof(f280,plain,
    ( spl3_24
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f56,f278])).

fof(f69,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))
    | ~ spl3_8 ),
    inference(superposition,[],[f57,f57])).

fof(f226,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f74,f56,f48,f31,f224])).

fof(f74,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f68,f32])).

fof(f68,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f57,f49])).

fof(f205,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f197,f194,f52,f48,f203])).

fof(f194,plain,
    ( spl3_20
  <=> ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f197,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f195,f132])).

fof(f132,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f53,f49])).

fof(f195,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f67,f56,f31,f194])).

fof(f67,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f57,f32])).

fof(f175,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f48,f35,f173])).

fof(f61,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f136,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f73,f56,f35,f134])).

fof(f73,plain,
    ( ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f36,f57])).

fof(f95,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f24,f93])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f91,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f23,f89])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f78,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f22,f76])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f19,f56])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f38,f35,f31,f52])).

fof(f38,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f36,f32])).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:31:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (10085)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (10086)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (10090)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (10095)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (10087)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (10096)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (10096)Refutation not found, incomplete strategy% (10096)------------------------------
% 0.21/0.48  % (10096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10096)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10096)Memory used [KB]: 10490
% 0.21/0.48  % (10096)Time elapsed: 0.061 s
% 0.21/0.48  % (10096)------------------------------
% 0.21/0.48  % (10096)------------------------------
% 0.21/0.49  % (10098)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (10088)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10097)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (10101)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (10100)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (10091)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10102)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (10094)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (10089)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (10092)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (10099)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (10093)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.42/0.58  % (10090)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % SZS output start Proof for theBenchmark
% 1.42/0.58  fof(f2395,plain,(
% 1.42/0.58    $false),
% 1.42/0.58    inference(avatar_sat_refutation,[],[f29,f33,f37,f42,f50,f54,f58,f78,f91,f95,f136,f175,f196,f205,f226,f280,f473,f479,f491,f666,f671,f789,f1245,f1347,f1513,f1800,f2321,f2382])).
% 1.42/0.58  fof(f2382,plain,(
% 1.42/0.58    ~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_14 | ~spl3_24 | ~spl3_34 | ~spl3_40 | ~spl3_43 | spl3_52 | ~spl3_56 | ~spl3_60 | ~spl3_68 | ~spl3_81),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f2381])).
% 1.42/0.58  fof(f2381,plain,(
% 1.42/0.58    $false | (~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_14 | ~spl3_24 | ~spl3_34 | ~spl3_40 | ~spl3_43 | spl3_52 | ~spl3_56 | ~spl3_60 | ~spl3_68 | ~spl3_81)),
% 1.42/0.58    inference(subsumption_resolution,[],[f1244,f2380])).
% 1.42/0.58  fof(f2380,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k4_xboole_0(X36,X37))) ) | (~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_14 | ~spl3_24 | ~spl3_34 | ~spl3_40 | ~spl3_43 | ~spl3_56 | ~spl3_60 | ~spl3_68 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2379,f1803])).
% 1.42/0.58  fof(f1803,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_68)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f36,f1799])).
% 1.42/0.58  fof(f1799,plain,(
% 1.42/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl3_68),
% 1.42/0.58    inference(avatar_component_clause,[],[f1798])).
% 1.42/0.58  fof(f1798,plain,(
% 1.42/0.58    spl3_68 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 1.42/0.58  fof(f36,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 1.42/0.58    inference(avatar_component_clause,[],[f35])).
% 1.42/0.58  fof(f35,plain,(
% 1.42/0.58    spl3_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.42/0.58  fof(f2379,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k3_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X36,X37)))) ) | (~spl3_9 | ~spl3_10 | ~spl3_14 | ~spl3_24 | ~spl3_34 | ~spl3_40 | ~spl3_43 | ~spl3_56 | ~spl3_60 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2378,f279])).
% 1.42/0.58  fof(f279,plain,(
% 1.42/0.58    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) ) | ~spl3_24),
% 1.42/0.58    inference(avatar_component_clause,[],[f278])).
% 1.42/0.58  fof(f278,plain,(
% 1.42/0.58    spl3_24 <=> ! [X3,X4] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.42/0.58  fof(f2378,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(X36,X37)))) ) | (~spl3_9 | ~spl3_10 | ~spl3_14 | ~spl3_34 | ~spl3_40 | ~spl3_43 | ~spl3_56 | ~spl3_60 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2377,f1525])).
% 1.42/0.58  fof(f1525,plain,(
% 1.42/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) ) | (~spl3_9 | ~spl3_60)),
% 1.42/0.58    inference(superposition,[],[f77,f1512])).
% 1.42/0.58  fof(f1512,plain,(
% 1.42/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl3_60),
% 1.42/0.58    inference(avatar_component_clause,[],[f1511])).
% 1.42/0.58  fof(f1511,plain,(
% 1.42/0.58    spl3_60 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.42/0.58  fof(f77,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl3_9),
% 1.42/0.58    inference(avatar_component_clause,[],[f76])).
% 1.42/0.58  fof(f76,plain,(
% 1.42/0.58    spl3_9 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.42/0.58  fof(f2377,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(X36,X37))))) ) | (~spl3_10 | ~spl3_14 | ~spl3_34 | ~spl3_40 | ~spl3_43 | ~spl3_56 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2376,f714])).
% 1.42/0.58  fof(f714,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | (~spl3_10 | ~spl3_14 | ~spl3_40)),
% 1.42/0.58    inference(forward_demodulation,[],[f681,f90])).
% 1.42/0.58  fof(f90,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_10),
% 1.42/0.58    inference(avatar_component_clause,[],[f89])).
% 1.42/0.58  fof(f89,plain,(
% 1.42/0.58    spl3_10 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.42/0.58  fof(f681,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | (~spl3_14 | ~spl3_40)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f135,f670])).
% 1.42/0.58  fof(f670,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4) | ~r1_tarski(X2,X3)) ) | ~spl3_40),
% 1.42/0.58    inference(avatar_component_clause,[],[f669])).
% 1.42/0.58  fof(f669,plain,(
% 1.42/0.58    spl3_40 <=> ! [X3,X2,X4] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4) | ~r1_tarski(X2,X3))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.42/0.58  fof(f135,plain,(
% 1.42/0.58    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) ) | ~spl3_14),
% 1.42/0.58    inference(avatar_component_clause,[],[f134])).
% 1.42/0.58  fof(f134,plain,(
% 1.42/0.58    spl3_14 <=> ! [X5,X4] : r1_tarski(k3_xboole_0(X4,X5),X4)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.42/0.58  fof(f2376,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X35,k4_xboole_0(k3_xboole_0(X35,X36),X37)))) ) | (~spl3_10 | ~spl3_14 | ~spl3_34 | ~spl3_40 | ~spl3_43 | ~spl3_56 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2375,f1348])).
% 1.42/0.58  fof(f1348,plain,(
% 1.42/0.58    ( ! [X12,X13,X11] : (k3_xboole_0(X12,k4_xboole_0(X11,X13)) = k3_xboole_0(X11,k4_xboole_0(X12,X13))) ) | (~spl3_10 | ~spl3_14 | ~spl3_34 | ~spl3_40 | ~spl3_56)),
% 1.42/0.58    inference(subsumption_resolution,[],[f715,f1346])).
% 1.42/0.58  fof(f1346,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl3_56),
% 1.42/0.58    inference(avatar_component_clause,[],[f1345])).
% 1.42/0.58  fof(f1345,plain,(
% 1.42/0.58    spl3_56 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.42/0.58  fof(f715,plain,(
% 1.42/0.58    ( ! [X12,X13,X11] : (k3_xboole_0(X12,k4_xboole_0(X11,X13)) = k3_xboole_0(X11,k4_xboole_0(X12,X13)) | ~r1_tarski(k3_xboole_0(X11,X12),X12)) ) | (~spl3_10 | ~spl3_14 | ~spl3_34 | ~spl3_40)),
% 1.42/0.58    inference(forward_demodulation,[],[f693,f714])).
% 1.42/0.58  fof(f693,plain,(
% 1.42/0.58    ( ! [X12,X13,X11] : (k4_xboole_0(k3_xboole_0(X11,X12),X13) = k3_xboole_0(X12,k4_xboole_0(X11,X13)) | ~r1_tarski(k3_xboole_0(X11,X12),X12)) ) | (~spl3_34 | ~spl3_40)),
% 1.42/0.58    inference(superposition,[],[f670,f490])).
% 1.42/0.58  fof(f490,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) ) | ~spl3_34),
% 1.42/0.58    inference(avatar_component_clause,[],[f489])).
% 1.42/0.58  fof(f489,plain,(
% 1.42/0.58    spl3_34 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.42/0.58  fof(f2375,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X37))) = k4_xboole_0(X35,k3_xboole_0(X36,k4_xboole_0(X35,X37)))) ) | (~spl3_43 | ~spl3_81)),
% 1.42/0.58    inference(forward_demodulation,[],[f2354,f788])).
% 1.42/0.58  fof(f788,plain,(
% 1.42/0.58    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6))) ) | ~spl3_43),
% 1.42/0.58    inference(avatar_component_clause,[],[f787])).
% 1.42/0.58  fof(f787,plain,(
% 1.42/0.58    spl3_43 <=> ! [X5,X7,X6] : k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.42/0.58  fof(f2354,plain,(
% 1.42/0.58    ( ! [X37,X35,X36] : (k4_xboole_0(X35,k3_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X37))) = k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X37))) ) | (~spl3_43 | ~spl3_81)),
% 1.42/0.58    inference(superposition,[],[f788,f2320])).
% 1.42/0.58  fof(f2320,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_81),
% 1.42/0.58    inference(avatar_component_clause,[],[f2319])).
% 1.42/0.58  fof(f2319,plain,(
% 1.42/0.58    spl3_81 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 1.42/0.58  fof(f1244,plain,(
% 1.42/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | spl3_52),
% 1.42/0.58    inference(avatar_component_clause,[],[f1242])).
% 1.42/0.58  fof(f1242,plain,(
% 1.42/0.58    spl3_52 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.42/0.58  fof(f2321,plain,(
% 1.42/0.58    spl3_81 | ~spl3_7 | ~spl3_40),
% 1.42/0.58    inference(avatar_split_clause,[],[f680,f669,f52,f2319])).
% 1.42/0.58  fof(f52,plain,(
% 1.42/0.58    spl3_7 <=> ! [X0] : r1_tarski(X0,X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.42/0.58  fof(f680,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl3_7 | ~spl3_40)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f53,f670])).
% 1.42/0.58  fof(f53,plain,(
% 1.42/0.58    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_7),
% 1.42/0.58    inference(avatar_component_clause,[],[f52])).
% 1.42/0.58  fof(f1800,plain,(
% 1.42/0.58    spl3_68 | ~spl3_4 | ~spl3_22),
% 1.42/0.58    inference(avatar_split_clause,[],[f230,f224,f40,f1798])).
% 1.42/0.58  fof(f40,plain,(
% 1.42/0.58    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.42/0.58  fof(f224,plain,(
% 1.42/0.58    spl3_22 <=> ! [X1,X2] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.42/0.58  fof(f230,plain,(
% 1.42/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl3_4 | ~spl3_22)),
% 1.42/0.58    inference(superposition,[],[f225,f41])).
% 1.42/0.58  fof(f41,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 1.42/0.58    inference(avatar_component_clause,[],[f40])).
% 1.42/0.58  fof(f225,plain,(
% 1.42/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | ~spl3_22),
% 1.42/0.58    inference(avatar_component_clause,[],[f224])).
% 1.42/0.58  fof(f1513,plain,(
% 1.42/0.58    spl3_60 | ~spl3_7 | ~spl3_22),
% 1.42/0.58    inference(avatar_split_clause,[],[f228,f224,f52,f1511])).
% 1.42/0.58  fof(f228,plain,(
% 1.42/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl3_7 | ~spl3_22)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f53,f225])).
% 1.42/0.58  fof(f1347,plain,(
% 1.42/0.58    spl3_56 | ~spl3_4 | ~spl3_14),
% 1.42/0.58    inference(avatar_split_clause,[],[f138,f134,f40,f1345])).
% 1.42/0.58  fof(f138,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl3_4 | ~spl3_14)),
% 1.42/0.58    inference(superposition,[],[f135,f41])).
% 1.42/0.58  fof(f1245,plain,(
% 1.42/0.58    ~spl3_52 | spl3_1 | ~spl3_43),
% 1.42/0.58    inference(avatar_split_clause,[],[f807,f787,f26,f1242])).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    spl3_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.42/0.58  fof(f807,plain,(
% 1.42/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | (spl3_1 | ~spl3_43)),
% 1.42/0.58    inference(superposition,[],[f28,f788])).
% 1.42/0.58  fof(f28,plain,(
% 1.42/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | spl3_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f26])).
% 1.42/0.58  fof(f789,plain,(
% 1.42/0.58    spl3_43 | ~spl3_8 | ~spl3_11),
% 1.42/0.58    inference(avatar_split_clause,[],[f127,f93,f56,f787])).
% 1.42/0.58  fof(f56,plain,(
% 1.42/0.58    spl3_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.42/0.58  fof(f93,plain,(
% 1.42/0.58    spl3_11 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.42/0.58  fof(f127,plain,(
% 1.42/0.58    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k3_xboole_0(X7,k4_xboole_0(X5,X6))) = k2_xboole_0(k4_xboole_0(X5,X7),k3_xboole_0(X5,X6))) ) | (~spl3_8 | ~spl3_11)),
% 1.42/0.58    inference(superposition,[],[f94,f57])).
% 1.42/0.58  fof(f57,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_8),
% 1.42/0.58    inference(avatar_component_clause,[],[f56])).
% 1.42/0.58  fof(f94,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ) | ~spl3_11),
% 1.42/0.58    inference(avatar_component_clause,[],[f93])).
% 1.42/0.58  fof(f671,plain,(
% 1.42/0.58    spl3_40 | ~spl3_19 | ~spl3_33 | ~spl3_39),
% 1.42/0.58    inference(avatar_split_clause,[],[f667,f664,f477,f173,f669])).
% 1.42/0.58  fof(f173,plain,(
% 1.42/0.58    spl3_19 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.42/0.58  fof(f477,plain,(
% 1.42/0.58    spl3_33 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.42/0.58  fof(f664,plain,(
% 1.42/0.58    spl3_39 <=> ! [X3,X2,X4] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4)) | ~r1_tarski(X2,X3))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.42/0.58  fof(f667,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k4_xboole_0(X2,X4) | ~r1_tarski(X2,X3)) ) | (~spl3_19 | ~spl3_33 | ~spl3_39)),
% 1.42/0.58    inference(forward_demodulation,[],[f665,f486])).
% 1.42/0.58  fof(f486,plain,(
% 1.42/0.58    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X10,X11))) ) | (~spl3_19 | ~spl3_33)),
% 1.42/0.58    inference(superposition,[],[f478,f174])).
% 1.42/0.58  fof(f174,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_19),
% 1.42/0.58    inference(avatar_component_clause,[],[f173])).
% 1.42/0.58  fof(f478,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | ~spl3_33),
% 1.42/0.58    inference(avatar_component_clause,[],[f477])).
% 1.42/0.58  fof(f665,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4)) | ~r1_tarski(X2,X3)) ) | ~spl3_39),
% 1.42/0.58    inference(avatar_component_clause,[],[f664])).
% 1.42/0.58  fof(f666,plain,(
% 1.42/0.58    spl3_39 | ~spl3_6 | ~spl3_11),
% 1.42/0.58    inference(avatar_split_clause,[],[f122,f93,f48,f664])).
% 1.42/0.58  fof(f48,plain,(
% 1.42/0.58    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.42/0.58  fof(f122,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X4)) | ~r1_tarski(X2,X3)) ) | (~spl3_6 | ~spl3_11)),
% 1.42/0.58    inference(superposition,[],[f94,f49])).
% 1.42/0.58  fof(f49,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 1.42/0.58    inference(avatar_component_clause,[],[f48])).
% 1.42/0.58  fof(f491,plain,(
% 1.42/0.58    spl3_34 | ~spl3_4 | ~spl3_10),
% 1.42/0.58    inference(avatar_split_clause,[],[f105,f89,f40,f489])).
% 1.42/0.58  fof(f105,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) ) | (~spl3_4 | ~spl3_10)),
% 1.42/0.58    inference(superposition,[],[f90,f41])).
% 1.42/0.58  fof(f479,plain,(
% 1.42/0.58    spl3_33 | ~spl3_2 | ~spl3_21 | ~spl3_32),
% 1.42/0.58    inference(avatar_split_clause,[],[f475,f471,f203,f31,f477])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    spl3_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.42/0.58  fof(f203,plain,(
% 1.42/0.58    spl3_21 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.42/0.58  fof(f471,plain,(
% 1.42/0.58    spl3_32 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.42/0.58  fof(f475,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | (~spl3_2 | ~spl3_21 | ~spl3_32)),
% 1.42/0.58    inference(forward_demodulation,[],[f474,f32])).
% 1.42/0.58  fof(f32,plain,(
% 1.42/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 1.42/0.58    inference(avatar_component_clause,[],[f31])).
% 1.42/0.58  fof(f474,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_21 | ~spl3_32)),
% 1.42/0.58    inference(forward_demodulation,[],[f472,f204])).
% 1.42/0.58  fof(f204,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_21),
% 1.42/0.58    inference(avatar_component_clause,[],[f203])).
% 1.42/0.58  fof(f472,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_32),
% 1.42/0.58    inference(avatar_component_clause,[],[f471])).
% 1.42/0.58  fof(f473,plain,(
% 1.42/0.58    spl3_32 | ~spl3_2 | ~spl3_11),
% 1.42/0.58    inference(avatar_split_clause,[],[f125,f93,f31,f471])).
% 1.42/0.58  fof(f125,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_2 | ~spl3_11)),
% 1.42/0.58    inference(superposition,[],[f94,f32])).
% 1.42/0.58  fof(f280,plain,(
% 1.42/0.58    spl3_24 | ~spl3_8),
% 1.42/0.58    inference(avatar_split_clause,[],[f69,f56,f278])).
% 1.42/0.58  fof(f69,plain,(
% 1.42/0.58    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) ) | ~spl3_8),
% 1.42/0.58    inference(superposition,[],[f57,f57])).
% 1.42/0.58  fof(f226,plain,(
% 1.42/0.58    spl3_22 | ~spl3_2 | ~spl3_6 | ~spl3_8),
% 1.42/0.58    inference(avatar_split_clause,[],[f74,f56,f48,f31,f224])).
% 1.42/0.58  fof(f74,plain,(
% 1.42/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | (~spl3_2 | ~spl3_6 | ~spl3_8)),
% 1.42/0.58    inference(forward_demodulation,[],[f68,f32])).
% 1.42/0.58  fof(f68,plain,(
% 1.42/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl3_6 | ~spl3_8)),
% 1.42/0.58    inference(superposition,[],[f57,f49])).
% 1.42/0.58  fof(f205,plain,(
% 1.42/0.58    spl3_21 | ~spl3_6 | ~spl3_7 | ~spl3_20),
% 1.42/0.58    inference(avatar_split_clause,[],[f197,f194,f52,f48,f203])).
% 1.42/0.58  fof(f194,plain,(
% 1.42/0.58    spl3_20 <=> ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.42/0.58  fof(f197,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_20)),
% 1.42/0.58    inference(forward_demodulation,[],[f195,f132])).
% 1.42/0.58  fof(f132,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_6 | ~spl3_7)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f53,f49])).
% 1.42/0.58  fof(f195,plain,(
% 1.42/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | ~spl3_20),
% 1.42/0.58    inference(avatar_component_clause,[],[f194])).
% 1.42/0.58  fof(f196,plain,(
% 1.42/0.58    spl3_20 | ~spl3_2 | ~spl3_8),
% 1.42/0.58    inference(avatar_split_clause,[],[f67,f56,f31,f194])).
% 1.42/0.58  fof(f67,plain,(
% 1.42/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl3_2 | ~spl3_8)),
% 1.42/0.58    inference(superposition,[],[f57,f32])).
% 1.42/0.58  fof(f175,plain,(
% 1.42/0.58    spl3_19 | ~spl3_3 | ~spl3_6),
% 1.42/0.58    inference(avatar_split_clause,[],[f61,f48,f35,f173])).
% 1.42/0.58  fof(f61,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_6)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f36,f49])).
% 1.42/0.58  fof(f136,plain,(
% 1.42/0.58    spl3_14 | ~spl3_3 | ~spl3_8),
% 1.42/0.58    inference(avatar_split_clause,[],[f73,f56,f35,f134])).
% 1.42/0.58  fof(f73,plain,(
% 1.42/0.58    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) ) | (~spl3_3 | ~spl3_8)),
% 1.42/0.58    inference(superposition,[],[f36,f57])).
% 1.42/0.58  fof(f95,plain,(
% 1.42/0.58    spl3_11),
% 1.42/0.58    inference(avatar_split_clause,[],[f24,f93])).
% 1.42/0.58  fof(f24,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f2])).
% 1.42/0.58  fof(f2,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.42/0.58  fof(f91,plain,(
% 1.42/0.58    spl3_10),
% 1.42/0.58    inference(avatar_split_clause,[],[f23,f89])).
% 1.42/0.58  fof(f23,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f8])).
% 1.42/0.58  fof(f8,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.42/0.58  fof(f78,plain,(
% 1.42/0.58    spl3_9),
% 1.42/0.58    inference(avatar_split_clause,[],[f22,f76])).
% 1.42/0.58  fof(f22,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f3])).
% 1.42/0.58  fof(f3,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.42/0.58  fof(f58,plain,(
% 1.42/0.58    spl3_8),
% 1.42/0.58    inference(avatar_split_clause,[],[f19,f56])).
% 1.42/0.58  fof(f19,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.42/0.58  fof(f54,plain,(
% 1.42/0.58    spl3_7 | ~spl3_2 | ~spl3_3),
% 1.42/0.58    inference(avatar_split_clause,[],[f38,f35,f31,f52])).
% 1.42/0.58  fof(f38,plain,(
% 1.42/0.58    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_2 | ~spl3_3)),
% 1.42/0.58    inference(superposition,[],[f36,f32])).
% 1.42/0.58  fof(f50,plain,(
% 1.42/0.58    spl3_6),
% 1.42/0.58    inference(avatar_split_clause,[],[f21,f48])).
% 1.42/0.58  fof(f21,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f14])).
% 1.42/0.58  fof(f14,plain,(
% 1.42/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.42/0.58    inference(nnf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.42/0.58  fof(f42,plain,(
% 1.42/0.58    spl3_4),
% 1.42/0.58    inference(avatar_split_clause,[],[f18,f40])).
% 1.42/0.58  fof(f18,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f1])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    spl3_3),
% 1.42/0.58    inference(avatar_split_clause,[],[f17,f35])).
% 1.42/0.58  fof(f17,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.42/0.58  fof(f33,plain,(
% 1.42/0.58    spl3_2),
% 1.42/0.58    inference(avatar_split_clause,[],[f16,f31])).
% 1.42/0.58  fof(f16,plain,(
% 1.42/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f6])).
% 1.42/0.58  fof(f6,axiom,(
% 1.42/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ~spl3_1),
% 1.42/0.58    inference(avatar_split_clause,[],[f15,f26])).
% 1.42/0.58  fof(f15,plain,(
% 1.42/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.42/0.58    inference(cnf_transformation,[],[f13])).
% 1.42/0.58  fof(f13,plain,(
% 1.42/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 1.42/0.58  fof(f12,plain,(
% 1.42/0.58    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f11,plain,(
% 1.42/0.58    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.58    inference(ennf_transformation,[],[f10])).
% 1.42/0.58  fof(f10,negated_conjecture,(
% 1.42/0.58    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.58    inference(negated_conjecture,[],[f9])).
% 1.42/0.58  fof(f9,conjecture,(
% 1.42/0.58    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (10090)------------------------------
% 1.42/0.58  % (10090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (10090)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (10090)Memory used [KB]: 8955
% 1.42/0.58  % (10090)Time elapsed: 0.160 s
% 1.42/0.58  % (10090)------------------------------
% 1.42/0.58  % (10090)------------------------------
% 1.42/0.59  % (10084)Success in time 0.214 s
%------------------------------------------------------------------------------
