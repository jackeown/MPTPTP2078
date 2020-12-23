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
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 14.63s
% Output     : Refutation 15.23s
% Verified   : 
% Statistics : Number of formulae       :  398 (158379 expanded)
%              Number of leaves         :   71 (43862 expanded)
%              Depth                    :   26
%              Number of atoms          :  774 (307122 expanded)
%              Number of equality atoms :  137 (112531 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f120,f128,f129,f136,f141,f186,f444,f562,f575,f584,f593,f598,f612,f704,f737,f739,f786,f788,f794,f822,f823,f824,f827,f834,f835,f836,f845,f1106,f1111,f1116,f1140,f1145,f1151,f1162,f1742,f1747,f1751,f1771,f1776,f1777,f1782,f1817,f1831,f1834,f2277,f2304,f2323,f2328,f2348,f2353,f2358,f2363,f7347,f7356,f7365,f7374,f7380,f10174,f10350,f10357,f10370,f10376,f10382,f10388,f10390])).

fof(f10390,plain,
    ( spl4_46
    | ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f10389])).

fof(f10389,plain,
    ( $false
    | spl4_46
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f10363,f1586])).

fof(f1586,plain,(
    ! [X8,X9] : k5_xboole_0(k5_xboole_0(X8,X9),X9) = X8 ),
    inference(superposition,[],[f1566,f1429])).

fof(f1429,plain,(
    ! [X2,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X2)) = X2 ),
    inference(backward_demodulation,[],[f755,f1411])).

fof(f1411,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f947,f1407])).

fof(f1407,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f1406,f724])).

fof(f724,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f387,f709])).

fof(f709,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))) ),
    inference(unit_resulting_resolution,[],[f313,f698])).

fof(f698,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f67,f64])).

fof(f64,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f61])).

% (6670)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f313,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))),X2) ),
    inference(superposition,[],[f225,f176])).

fof(f176,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(unit_resulting_resolution,[],[f162,f162,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f162,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f161,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f161,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k5_xboole_0(X3,X3)) ),
    inference(subsumption_resolution,[],[f157,f110])).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f84,f97])).

fof(f97,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f81,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f157,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f85,f97])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f225,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),X1) ),
    inference(unit_resulting_resolution,[],[f181,f41])).

fof(f181,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1)))) ),
    inference(backward_demodulation,[],[f169,f177])).

fof(f177,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f162,f35])).

fof(f169,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X1),X2)))) ),
    inference(forward_demodulation,[],[f163,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f163,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(k5_xboole_0(X1,X1),X2))) ),
    inference(unit_resulting_resolution,[],[f161,f85])).

fof(f387,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,X0) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X2))) ),
    inference(unit_resulting_resolution,[],[f162,f313,f39])).

fof(f1406,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f1384,f750])).

fof(f750,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f177,f724])).

fof(f1384,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f66,f64])).

fof(f66,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f61,f33])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f947,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f755,f724])).

fof(f755,plain,(
    ! [X2,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f239,f724])).

fof(f239,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X2)) = k5_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(superposition,[],[f48,f176])).

fof(f1566,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f1549,f1407])).

fof(f1549,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f1429,f756])).

fof(f756,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(backward_demodulation,[],[f242,f724])).

fof(f242,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X5,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f48,f176])).

fof(f10363,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_46
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f7379,f10349])).

fof(f10349,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f10347])).

fof(f10347,plain,
    ( spl4_48
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f7379,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f7377])).

fof(f7377,plain,
    ( spl4_46
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f10388,plain,
    ( ~ spl4_53
    | spl4_45
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f10383,f10347,f7371,f10385])).

fof(f10385,plain,
    ( spl4_53
  <=> r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f7371,plain,
    ( spl4_45
  <=> r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f10383,plain,
    ( ~ r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_45
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f10362,f1429])).

fof(f10362,plain,
    ( ~ r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_45
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f7373,f10349])).

fof(f7373,plain,
    ( ~ r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f7371])).

fof(f10382,plain,
    ( spl4_52
    | ~ spl4_44
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f10377,f10347,f7362,f10379])).

fof(f10379,plain,
    ( spl4_52
  <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f7362,plain,
    ( spl4_44
  <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f10377,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))
    | ~ spl4_44
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f10361,f1429])).

fof(f10361,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))
    | ~ spl4_44
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f7364,f10349])).

fof(f7364,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f7362])).

fof(f10376,plain,
    ( ~ spl4_51
    | spl4_43
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f10371,f10347,f7353,f10373])).

fof(f10373,plain,
    ( spl4_51
  <=> r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f7353,plain,
    ( spl4_43
  <=> r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f10371,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))
    | spl4_43
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f10360,f1429])).

fof(f10360,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))
    | spl4_43
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f7355,f10349])).

fof(f7355,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f7353])).

fof(f10370,plain,
    ( spl4_50
    | ~ spl4_42
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f10365,f10347,f7344,f10367])).

fof(f10367,plain,
    ( spl4_50
  <=> r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f7344,plain,
    ( spl4_42
  <=> r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f10365,plain,
    ( r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))
    | ~ spl4_42
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f10359,f1429])).

fof(f10359,plain,
    ( r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))
    | ~ spl4_42
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f7346,f10349])).

fof(f7346,plain,
    ( r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f7344])).

fof(f10357,plain,
    ( ~ spl4_49
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f10352,f559,f88,f10354])).

fof(f10354,plain,
    ( spl4_49
  <=> sK1 = k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f88,plain,
    ( spl4_1
  <=> sK1 = k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f559,plain,
    ( spl4_9
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f10352,plain,
    ( sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f10344,f561])).

fof(f561,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f559])).

fof(f10344,plain,
    ( sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f90,f10193])).

fof(f10193,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f10192,f1566])).

fof(f10192,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,k5_xboole_0(X2,X3)) = k3_xboole_0(X3,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f10088,f1592])).

fof(f1592,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f1429,f1566])).

fof(f10088,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = k5_xboole_0(k5_xboole_0(X2,X3),X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f1431,f1386])).

fof(f1386,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f66,f67])).

fof(f1431,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(backward_demodulation,[],[f946,f1411])).

fof(f946,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f755,f48])).

fof(f90,plain,
    ( sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f10350,plain,
    ( spl4_48
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f10313,f559,f10347])).

fof(f10313,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f561,f10193])).

fof(f10174,plain,
    ( spl4_47
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f10060,f559,f10171])).

fof(f10171,plain,
    ( spl4_47
  <=> sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f10060,plain,
    ( sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f561,f1386])).

fof(f7380,plain,
    ( ~ spl4_46
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7375,f88,f7377])).

fof(f7375,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7336,f3144])).

fof(f3144,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))))) ),
    inference(unit_resulting_resolution,[],[f86,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f62,f33,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f60])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f56,f33,f62])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f7336,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))
    | spl4_1 ),
    inference(superposition,[],[f90,f66])).

fof(f7374,plain,
    ( ~ spl4_45
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7369,f88,f7371])).

fof(f7369,plain,
    ( ~ r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7368,f3573])).

fof(f3573,plain,(
    ! [X70,X71,X69] : k5_xboole_0(X71,k5_xboole_0(X69,X70)) = k5_xboole_0(X71,k5_xboole_0(X70,X69)) ),
    inference(forward_demodulation,[],[f3483,f1411])).

fof(f3483,plain,(
    ! [X70,X71,X69] : k5_xboole_0(X71,k5_xboole_0(X69,X70)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X71),k5_xboole_0(X70,X69)) ),
    inference(superposition,[],[f1622,f2667])).

fof(f2667,plain,(
    ! [X19,X18] : k5_xboole_0(X19,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,X19)) ),
    inference(superposition,[],[f2404,f724])).

fof(f2404,plain,(
    ! [X35,X33,X34] : k5_xboole_0(X34,X33) = k5_xboole_0(k5_xboole_0(X35,X33),k5_xboole_0(X35,X34)) ),
    inference(superposition,[],[f1431,f1566])).

fof(f1622,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10)) ),
    inference(superposition,[],[f48,f1585])).

fof(f1585,plain,(
    ! [X6,X7] : k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6 ),
    inference(superposition,[],[f1566,f1566])).

fof(f7368,plain,
    ( ~ r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7367,f2587])).

fof(f2587,plain,(
    ! [X43,X41,X42,X40] : k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X40,X42))) = k5_xboole_0(X40,k5_xboole_0(X43,k5_xboole_0(X41,X42))) ),
    inference(superposition,[],[f1607,f1607])).

fof(f1607,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X8,X10))) ),
    inference(forward_demodulation,[],[f1595,f48])).

fof(f1595,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,X8),X10)) ),
    inference(superposition,[],[f48,f1566])).

fof(f7367,plain,
    ( ~ r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7366,f1653])).

fof(f1653,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1592,f48])).

fof(f7366,plain,
    ( ~ r2_hidden(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7328,f66])).

fof(f7328,plain,
    ( ~ r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f90,f1750])).

fof(f1750,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k3_enumset1(X3,X3,X3,X3,X3))
      | X3 = X4 ) ),
    inference(subsumption_resolution,[],[f1733,f1729])).

fof(f1729,plain,(
    ! [X6,X7,X5] :
      ( X5 = X6
      | ~ r2_hidden(X5,X7)
      | ~ r2_hidden(X5,k3_enumset1(X6,X6,X6,X6,X6)) ) ),
    inference(resolution,[],[f78,f84])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f33,f62])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1733,plain,(
    ! [X4,X3] :
      ( r2_hidden(X4,k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X3,X3,X3,X3,X3)))
      | X3 = X4
      | ~ r2_hidden(X4,k3_enumset1(X3,X3,X3,X3,X3)) ) ),
    inference(superposition,[],[f78,f97])).

fof(f7365,plain,
    ( spl4_44
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7360,f88,f7362])).

fof(f7360,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7359,f3573])).

fof(f7359,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7358,f2587])).

fof(f7358,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7357,f1653])).

fof(f7357,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7329,f66])).

fof(f7329,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f438,f90,f78])).

fof(f438,plain,(
    ! [X0] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f7356,plain,
    ( ~ spl4_43
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7351,f88,f7353])).

fof(f7351,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7350,f3573])).

fof(f7350,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7349,f2587])).

fof(f7349,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7348,f1653])).

fof(f7348,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7330,f66])).

fof(f7330,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f90,f1750])).

fof(f7347,plain,
    ( spl4_42
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7342,f88,f7344])).

fof(f7342,plain,
    ( r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7341,f3573])).

fof(f7341,plain,
    ( r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7340,f2587])).

fof(f7340,plain,
    ( r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7339,f1653])).

fof(f7339,plain,
    ( r2_hidden(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7338,f66])).

fof(f7338,plain,
    ( r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f7331,f1550])).

fof(f1550,plain,(
    ! [X6,X7] : k5_xboole_0(X7,k3_xboole_0(X7,X6)) = k5_xboole_0(X6,k3_tarski(k3_enumset1(X6,X6,X6,X6,X7))) ),
    inference(superposition,[],[f1429,f66])).

fof(f7331,plain,
    ( r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f438,f90,f78])).

fof(f2363,plain,
    ( ~ spl4_41
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f2331,f791,f2360])).

fof(f2360,plain,
    ( spl4_41
  <=> k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f791,plain,
    ( spl4_19
  <=> r2_hidden(sK2(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f2331,plain,
    ( k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)) != k5_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1))
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f793,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f62,f33,f62])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f793,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f791])).

fof(f2358,plain,
    ( ~ spl4_40
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f2332,f590,f2355])).

fof(f2355,plain,
    ( spl4_40
  <=> k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f590,plain,
    ( spl4_13
  <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f2332,plain,
    ( k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f592,f70])).

fof(f592,plain,
    ( r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f590])).

fof(f2353,plain,
    ( ~ spl4_39
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f2333,f1773,f2350])).

fof(f2350,plain,
    ( spl4_39
  <=> k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)) = k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1773,plain,
    ( spl4_31
  <=> r2_hidden(sK2(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f2333,plain,
    ( k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)) != k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1))
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f1774,f70])).

fof(f1774,plain,
    ( r2_hidden(sK2(sK1,sK1),sK1)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f2348,plain,
    ( ~ spl4_38
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f2334,f2274,f2345])).

fof(f2345,plain,
    ( spl4_38
  <=> k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f2274,plain,
    ( spl4_34
  <=> r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f2334,plain,
    ( k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) != k5_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f2276,f70])).

fof(f2276,plain,
    ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f2274])).

fof(f2328,plain,
    ( ~ spl4_37
    | spl4_11 ),
    inference(avatar_split_clause,[],[f2307,f577,f2325])).

fof(f2325,plain,
    ( spl4_37
  <=> r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f577,plain,
    ( spl4_11
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f2307,plain,
    ( ~ r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f578,f1750])).

fof(f578,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f577])).

fof(f2323,plain,
    ( ~ spl4_36
    | spl4_11 ),
    inference(avatar_split_clause,[],[f2308,f577,f2320])).

fof(f2320,plain,
    ( spl4_36
  <=> r2_hidden(sK1,k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f2308,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f578,f1750])).

fof(f2304,plain,
    ( spl4_35
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f2294,f2274,f2301])).

fof(f2301,plain,
    ( spl4_35
  <=> r1_tarski(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f2294,plain,
    ( r1_tarski(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1)
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f2276,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2277,plain,
    ( spl4_34
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f2245,f559,f2274])).

fof(f2245,plain,
    ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f811,f561,f104])).

fof(f104,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK2(X1,X2),X3)
      | ~ r1_tarski(X1,X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f40,f41])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f811,plain,(
    ! [X0] : ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f435,f756])).

fof(f435,plain,(
    ! [X2,X0,X1] : ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ),
    inference(unit_resulting_resolution,[],[f248,f68])).

fof(f248,plain,(
    ! [X12,X13,X11] : ~ r2_hidden(X13,k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X12)))) ),
    inference(superposition,[],[f161,f48])).

fof(f1834,plain,
    ( spl4_32
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f1823,f1773,f1779])).

fof(f1779,plain,
    ( spl4_32
  <=> r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1823,plain,
    ( r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f1774,f69])).

fof(f1831,plain,
    ( ~ spl4_31
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f1830])).

fof(f1830,plain,
    ( $false
    | ~ spl4_31
    | spl4_32 ),
    inference(subsumption_resolution,[],[f1823,f1780])).

fof(f1780,plain,
    ( ~ r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1817,plain,
    ( spl4_33
    | spl4_31 ),
    inference(avatar_split_clause,[],[f1812,f1773,f1814])).

fof(f1814,plain,
    ( spl4_33
  <=> r2_hidden(sK2(sK1,sK1),k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1812,plain,
    ( r2_hidden(sK2(sK1,sK1),k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1))))))
    | spl4_31 ),
    inference(forward_demodulation,[],[f1805,f1550])).

fof(f1805,plain,
    ( r2_hidden(sK2(sK1,sK1),k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)))
    | spl4_31 ),
    inference(unit_resulting_resolution,[],[f438,f1775,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1775,plain,
    ( ~ r2_hidden(sK2(sK1,sK1),sK1)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1782,plain,
    ( spl4_32
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f1759,f609,f577,f1779])).

fof(f609,plain,
    ( spl4_15
  <=> r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1759,plain,
    ( r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f611,f579])).

fof(f579,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f577])).

fof(f611,plain,
    ( r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f609])).

fof(f1777,plain,
    ( ~ spl4_31
    | ~ spl4_11
    | spl4_14 ),
    inference(avatar_split_clause,[],[f1758,f595,f577,f1773])).

fof(f595,plain,
    ( spl4_14
  <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1758,plain,
    ( ~ r2_hidden(sK2(sK1,sK1),sK1)
    | ~ spl4_11
    | spl4_14 ),
    inference(backward_demodulation,[],[f597,f579])).

fof(f597,plain,
    ( ~ r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1776,plain,
    ( ~ spl4_31
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1757,f590,f577,f1773])).

fof(f1757,plain,
    ( ~ r2_hidden(sK2(sK1,sK1),sK1)
    | ~ spl4_11
    | spl4_13 ),
    inference(backward_demodulation,[],[f591,f579])).

fof(f591,plain,
    ( ~ r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f590])).

fof(f1771,plain,
    ( spl4_1
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f1770])).

fof(f1770,plain,
    ( $false
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1769,f815])).

fof(f815,plain,(
    ! [X2] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2 ),
    inference(backward_demodulation,[],[f695,f756])).

fof(f695,plain,(
    ! [X2,X0,X1] : k3_tarski(k3_enumset1(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),X2)) = X2 ),
    inference(unit_resulting_resolution,[],[f249,f67])).

fof(f249,plain,(
    ! [X14,X15,X16] : r1_tarski(k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X15))),X16) ),
    inference(superposition,[],[f162,f48])).

fof(f1769,plain,
    ( sK1 != k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | spl4_1
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1768,f724])).

fof(f1768,plain,
    ( sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),sK1))
    | spl4_1
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1752,f97])).

fof(f1752,plain,
    ( sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1))
    | spl4_1
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f90,f579])).

fof(f1751,plain,
    ( spl4_13
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1515,f1108,f590])).

fof(f1108,plain,
    ( spl4_23
  <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1515,plain,
    ( r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f1110,f1507])).

fof(f1507,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f1487,f815])).

fof(f1487,plain,(
    ! [X2] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f1411,f66])).

fof(f1110,plain,
    ( r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1747,plain,
    ( spl4_30
    | spl4_11 ),
    inference(avatar_split_clause,[],[f1720,f577,f1744])).

fof(f1744,plain,
    ( spl4_30
  <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1720,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f438,f578,f78])).

fof(f1742,plain,
    ( spl4_29
    | spl4_11 ),
    inference(avatar_split_clause,[],[f1737,f577,f1739])).

fof(f1739,plain,
    ( spl4_29
  <=> r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1737,plain,
    ( r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))
    | spl4_11 ),
    inference(forward_demodulation,[],[f1721,f1550])).

fof(f1721,plain,
    ( r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f438,f578,f78])).

fof(f1162,plain,
    ( spl4_28
    | spl4_25 ),
    inference(avatar_split_clause,[],[f1156,f1137,f1159])).

fof(f1159,plain,
    ( spl4_28
  <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1137,plain,
    ( spl4_25
  <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1156,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f1139,f41])).

fof(f1139,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f1137])).

fof(f1151,plain,
    ( spl4_27
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1146,f1113,f1148])).

fof(f1148,plain,
    ( spl4_27
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1113,plain,
    ( spl4_24
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1146,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0))))
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f1122,f48])).

fof(f1122,plain,
    ( r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f716,f1115,f83])).

fof(f1115,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f716,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f181,f709])).

fof(f1145,plain,
    ( spl4_26
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1125,f1113,f1142])).

fof(f1142,plain,
    ( spl4_26
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1125,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f1115,f69])).

fof(f1140,plain,
    ( ~ spl4_25
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1130,f1113,f1137])).

fof(f1130,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f716,f1115,f40])).

fof(f1116,plain,
    ( spl4_24
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1081,f93,f1113])).

fof(f93,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1081,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f95,f716,f83])).

fof(f95,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1111,plain,
    ( spl4_23
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f1083,f590,f1108])).

fof(f1083,plain,
    ( r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f592,f716,f83])).

fof(f1106,plain,
    ( spl4_22
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f1084,f791,f1103])).

fof(f1103,plain,
    ( spl4_22
  <=> r2_hidden(sK2(sK1,k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1084,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f793,f716,f83])).

fof(f845,plain,
    ( spl4_19
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f731,f93,f791])).

fof(f731,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f479,f709])).

fof(f479,plain,
    ( ! [X0,X1] : r2_hidden(sK2(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))),sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f358,f41])).

fof(f358,plain,
    ( ! [X0,X1] : ~ r1_tarski(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f234,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f40,f95])).

fof(f234,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))) ),
    inference(superposition,[],[f181,f176])).

fof(f836,plain,
    ( spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f773,f133,f791])).

fof(f133,plain,
    ( spl4_5
  <=> r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f773,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f135,f724])).

fof(f135,plain,
    ( r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f835,plain,
    ( ~ spl4_17
    | spl4_4 ),
    inference(avatar_split_clause,[],[f772,f125,f734])).

fof(f734,plain,
    ( spl4_17
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f125,plain,
    ( spl4_4
  <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f772,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl4_4 ),
    inference(backward_demodulation,[],[f127,f724])).

fof(f127,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f834,plain,
    ( spl4_21
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f765,f93,f831])).

fof(f831,plain,
    ( spl4_21
  <=> r1_tarski(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f765,plain,
    ( r1_tarski(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f550,f724])).

fof(f550,plain,
    ( ! [X0] : r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0))),sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f188,f69])).

fof(f188,plain,
    ( ! [X0] : r2_hidden(sK2(sK1,k5_xboole_0(X0,X0)),sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f167,f41])).

fof(f167,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k5_xboole_0(X0,X0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f161,f103])).

fof(f827,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f826,f93,f734])).

fof(f826,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f816,f724])).

fof(f816,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f795,f756])).

fof(f795,plain,
    ( ! [X6,X7] : ~ r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(X6,X7)))))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f482,f755])).

fof(f482,plain,
    ( ! [X6,X8,X7] : ~ r1_tarski(sK1,k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(X6,X7))))))
    | ~ spl4_2 ),
    inference(superposition,[],[f358,f48])).

fof(f824,plain,
    ( spl4_19
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f805,f93,f791])).

fof(f805,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f254,f756])).

fof(f254,plain,
    ( ! [X28,X29] : r2_hidden(sK2(sK1,k5_xboole_0(X28,k5_xboole_0(X29,k5_xboole_0(X28,X29)))),sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f188,f48])).

fof(f823,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f804,f93,f734])).

fof(f804,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f250,f756])).

fof(f250,plain,
    ( ! [X17,X18] : ~ r1_tarski(sK1,k5_xboole_0(X17,k5_xboole_0(X18,k5_xboole_0(X17,X18))))
    | ~ spl4_2 ),
    inference(superposition,[],[f167,f48])).

fof(f822,plain,
    ( spl4_20
    | ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f800,f93,f734,f820])).

fof(f820,plain,
    ( spl4_20
  <=> ! [X5,X6] : ~ r1_tarski(k5_xboole_0(X5,X6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f800,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK1,k1_xboole_0)
        | ~ r1_tarski(k5_xboole_0(X5,X6),sK1) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f246,f756])).

fof(f246,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK1,k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))))
        | ~ r1_tarski(k5_xboole_0(X5,X6),sK1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f144,f48])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k5_xboole_0(X0,X0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f112,f35])).

fof(f112,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f95,f107,f40])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f95,f84])).

fof(f794,plain,
    ( spl4_19
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f752,f93,f791])).

fof(f752,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f188,f724])).

fof(f788,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f748,f93,f734])).

fof(f748,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f167,f724])).

fof(f786,plain,
    ( spl4_18
    | ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f743,f93,f734,f784])).

fof(f784,plain,
    ( spl4_18
  <=> ! [X0] : ~ r1_tarski(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k1_xboole_0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f144,f724])).

fof(f739,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f723,f93,f734])).

fof(f723,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f358,f709])).

fof(f737,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f718,f93,f734])).

fof(f718,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f232,f709])).

fof(f232,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f181,f103])).

fof(f704,plain,
    ( spl4_16
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f697,f559,f701])).

fof(f701,plain,
    ( spl4_16
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f697,plain,
    ( sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f561,f67])).

fof(f612,plain,
    ( spl4_15
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f599,f590,f609])).

fof(f599,plain,
    ( r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f592,f69])).

fof(f598,plain,
    ( ~ spl4_14
    | spl4_12 ),
    inference(avatar_split_clause,[],[f587,f581,f595])).

fof(f581,plain,
    ( spl4_12
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f587,plain,
    ( ~ r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f583,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f583,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f581])).

fof(f593,plain,
    ( spl4_13
    | spl4_12 ),
    inference(avatar_split_clause,[],[f588,f581,f590])).

fof(f588,plain,
    ( r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f583,f41])).

fof(f584,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f570,f559,f581,f577])).

fof(f570,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f561,f39])).

fof(f575,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f568,f559,f572])).

fof(f572,plain,
    ( spl4_10
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f568,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f561,f35])).

fof(f562,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f548,f93,f559])).

fof(f548,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f95,f69])).

fof(f444,plain,
    ( ~ spl4_8
    | spl4_6 ),
    inference(avatar_split_clause,[],[f437,f138,f441])).

fof(f441,plain,
    ( spl4_8
  <=> r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1))),k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f138,plain,
    ( spl4_6
  <=> r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f437,plain,
    ( ~ r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1))),k5_xboole_0(sK1,sK1))
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f140,f68])).

fof(f140,plain,
    ( ~ r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f186,plain,
    ( ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f180,f117,f183])).

fof(f183,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f117,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f180,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | spl4_3 ),
    inference(backward_demodulation,[],[f158,f177])).

fof(f158,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))
    | spl4_3 ),
    inference(forward_demodulation,[],[f154,f48])).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f119,f85])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f141,plain,
    ( ~ spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f130,f125,f138])).

fof(f130,plain,
    ( ~ r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f127,f42])).

fof(f136,plain,
    ( spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f131,f125,f133])).

fof(f131,plain,
    ( r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f127,f41])).

fof(f129,plain,
    ( ~ spl4_4
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f121,f117,f93,f125])).

fof(f121,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f119,f103])).

fof(f128,plain,
    ( ~ spl4_4
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f122,f117,f93,f125])).

fof(f122,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f95,f119,f40])).

fof(f120,plain,
    ( ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f115,f93,f117])).

fof(f115,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f107,f97])).

fof(f96,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f93])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f91,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f88])).

fof(f63,plain,(
    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f27,f61,f33,f62,f62])).

fof(f27,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6619)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6626)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (6633)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (6620)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (6637)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (6621)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (6641)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (6637)Refutation not found, incomplete strategy% (6637)------------------------------
% 0.20/0.52  % (6637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6637)Memory used [KB]: 10746
% 0.20/0.52  % (6637)Time elapsed: 0.116 s
% 0.20/0.52  % (6637)------------------------------
% 0.20/0.52  % (6637)------------------------------
% 0.20/0.52  % (6627)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (6618)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (6645)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (6622)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (6634)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (6623)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (6617)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (6628)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (6643)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (6625)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (6642)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (6632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6631)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (6635)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (6644)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (6639)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (6646)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (6636)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (6629)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (6638)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (6624)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (6630)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (6640)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.07/0.63  % (6648)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.87/0.87  % (6622)Time limit reached!
% 3.87/0.87  % (6622)------------------------------
% 3.87/0.87  % (6622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.88  % (6622)Termination reason: Time limit
% 3.87/0.88  
% 3.87/0.88  % (6622)Memory used [KB]: 11001
% 3.87/0.88  % (6622)Time elapsed: 0.468 s
% 3.87/0.88  % (6622)------------------------------
% 3.87/0.88  % (6622)------------------------------
% 4.09/0.90  % (6629)Time limit reached!
% 4.09/0.90  % (6629)------------------------------
% 4.09/0.90  % (6629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.90  % (6629)Termination reason: Time limit
% 4.09/0.90  % (6629)Termination phase: Saturation
% 4.09/0.90  
% 4.09/0.90  % (6629)Memory used [KB]: 8571
% 4.09/0.90  % (6629)Time elapsed: 0.500 s
% 4.09/0.90  % (6629)------------------------------
% 4.09/0.90  % (6629)------------------------------
% 4.09/0.90  % (6618)Time limit reached!
% 4.09/0.90  % (6618)------------------------------
% 4.09/0.90  % (6618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.90  % (6618)Termination reason: Time limit
% 4.09/0.90  % (6618)Termination phase: Saturation
% 4.09/0.90  
% 4.09/0.90  % (6618)Memory used [KB]: 9722
% 4.09/0.90  % (6618)Time elapsed: 0.500 s
% 4.09/0.90  % (6618)------------------------------
% 4.09/0.90  % (6618)------------------------------
% 4.09/0.91  % (6627)Time limit reached!
% 4.09/0.91  % (6627)------------------------------
% 4.09/0.91  % (6627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.91  % (6634)Time limit reached!
% 4.09/0.91  % (6634)------------------------------
% 4.09/0.91  % (6634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.91  % (6634)Termination reason: Time limit
% 4.09/0.91  % (6634)Termination phase: Saturation
% 4.09/0.91  
% 4.09/0.91  % (6634)Memory used [KB]: 14072
% 4.09/0.91  % (6634)Time elapsed: 0.500 s
% 4.09/0.91  % (6634)------------------------------
% 4.09/0.91  % (6634)------------------------------
% 4.09/0.91  % (6627)Termination reason: Time limit
% 4.09/0.91  % (6627)Termination phase: Saturation
% 4.09/0.91  
% 4.09/0.91  % (6627)Memory used [KB]: 14839
% 4.09/0.91  % (6627)Time elapsed: 0.500 s
% 4.09/0.91  % (6627)------------------------------
% 4.09/0.91  % (6627)------------------------------
% 4.09/0.92  % (6617)Time limit reached!
% 4.09/0.92  % (6617)------------------------------
% 4.09/0.92  % (6617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (6617)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (6617)Memory used [KB]: 3582
% 4.45/0.93  % (6617)Time elapsed: 0.514 s
% 4.45/0.93  % (6617)------------------------------
% 4.45/0.93  % (6617)------------------------------
% 4.55/1.00  % (6649)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.98/1.01  % (6650)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.98/1.03  % (6633)Time limit reached!
% 4.98/1.03  % (6633)------------------------------
% 4.98/1.03  % (6633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.03  % (6633)Termination reason: Time limit
% 4.98/1.03  
% 4.98/1.03  % (6633)Memory used [KB]: 18421
% 4.98/1.03  % (6633)Time elapsed: 0.622 s
% 4.98/1.03  % (6633)------------------------------
% 4.98/1.03  % (6633)------------------------------
% 4.98/1.04  % (6653)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.98/1.04  % (6652)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.98/1.04  % (6624)Time limit reached!
% 4.98/1.04  % (6624)------------------------------
% 4.98/1.04  % (6624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.04  % (6624)Termination reason: Time limit
% 4.98/1.04  
% 4.98/1.04  % (6624)Memory used [KB]: 12920
% 4.98/1.04  % (6624)Time elapsed: 0.639 s
% 4.98/1.04  % (6624)------------------------------
% 4.98/1.04  % (6624)------------------------------
% 4.98/1.05  % (6651)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.98/1.06  % (6654)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.98/1.07  % (6645)Time limit reached!
% 4.98/1.07  % (6645)------------------------------
% 4.98/1.07  % (6645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.07  % (6645)Termination reason: Time limit
% 4.98/1.07  
% 4.98/1.07  % (6645)Memory used [KB]: 9466
% 4.98/1.07  % (6645)Time elapsed: 0.610 s
% 4.98/1.07  % (6645)------------------------------
% 4.98/1.07  % (6645)------------------------------
% 5.64/1.16  % (6655)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.32/1.17  % (6656)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.54/1.22  % (6657)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.54/1.22  % (6638)Time limit reached!
% 6.54/1.22  % (6638)------------------------------
% 6.54/1.22  % (6638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.80/1.23  % (6638)Termination reason: Time limit
% 6.80/1.23  
% 6.80/1.23  % (6638)Memory used [KB]: 7675
% 6.80/1.23  % (6638)Time elapsed: 0.821 s
% 6.80/1.23  % (6638)------------------------------
% 6.80/1.23  % (6638)------------------------------
% 7.39/1.35  % (6651)Time limit reached!
% 7.39/1.35  % (6651)------------------------------
% 7.39/1.35  % (6651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.39/1.36  % (6651)Termination reason: Time limit
% 7.39/1.36  
% 7.39/1.36  % (6651)Memory used [KB]: 8059
% 7.39/1.36  % (6651)Time elapsed: 0.424 s
% 7.39/1.36  % (6651)------------------------------
% 7.39/1.36  % (6651)------------------------------
% 7.39/1.36  % (6652)Time limit reached!
% 7.39/1.36  % (6652)------------------------------
% 7.39/1.36  % (6652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.39/1.36  % (6652)Termination reason: Time limit
% 7.39/1.36  
% 7.39/1.36  % (6652)Memory used [KB]: 14072
% 7.39/1.36  % (6652)Time elapsed: 0.424 s
% 7.39/1.36  % (6652)------------------------------
% 7.39/1.36  % (6652)------------------------------
% 7.91/1.38  % (6658)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.91/1.42  % (6619)Time limit reached!
% 7.91/1.42  % (6619)------------------------------
% 7.91/1.42  % (6619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.43  % (6619)Termination reason: Time limit
% 7.91/1.43  
% 7.91/1.43  % (6619)Memory used [KB]: 24434
% 7.91/1.43  % (6619)Time elapsed: 1.014 s
% 7.91/1.43  % (6619)------------------------------
% 7.91/1.43  % (6619)------------------------------
% 7.91/1.46  % (6659)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.62/1.48  % (6660)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.04/1.55  % (6661)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.84/1.64  % (6643)Time limit reached!
% 9.84/1.64  % (6643)------------------------------
% 9.84/1.64  % (6643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.84/1.64  % (6643)Termination reason: Time limit
% 9.84/1.64  
% 9.84/1.64  % (6643)Memory used [KB]: 20212
% 9.84/1.64  % (6643)Time elapsed: 1.244 s
% 9.84/1.64  % (6643)------------------------------
% 9.84/1.64  % (6643)------------------------------
% 9.84/1.67  % (6639)Time limit reached!
% 9.84/1.67  % (6639)------------------------------
% 9.84/1.67  % (6639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.84/1.68  % (6639)Termination reason: Time limit
% 9.84/1.68  % (6639)Termination phase: Saturation
% 9.84/1.68  
% 9.84/1.68  % (6639)Memory used [KB]: 16502
% 9.84/1.68  % (6639)Time elapsed: 1.200 s
% 9.84/1.68  % (6639)------------------------------
% 9.84/1.68  % (6639)------------------------------
% 10.43/1.72  % (6632)Time limit reached!
% 10.43/1.72  % (6632)------------------------------
% 10.43/1.72  % (6632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.73  % (6632)Termination reason: Time limit
% 10.43/1.73  
% 10.43/1.73  % (6632)Memory used [KB]: 12920
% 10.43/1.73  % (6632)Time elapsed: 1.320 s
% 10.43/1.73  % (6632)------------------------------
% 10.43/1.73  % (6632)------------------------------
% 10.43/1.77  % (6641)Time limit reached!
% 10.43/1.77  % (6641)------------------------------
% 10.43/1.77  % (6641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.77  % (6641)Termination reason: Time limit
% 10.43/1.77  % (6641)Termination phase: Saturation
% 10.43/1.77  
% 10.43/1.77  % (6641)Memory used [KB]: 20724
% 10.43/1.77  % (6641)Time elapsed: 1.300 s
% 10.43/1.77  % (6641)------------------------------
% 10.43/1.77  % (6641)------------------------------
% 11.12/1.78  % (6663)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.26/1.80  % (6662)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.42/1.83  % (6664)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.99/1.90  % (6660)Time limit reached!
% 11.99/1.90  % (6660)------------------------------
% 11.99/1.90  % (6660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.99/1.90  % (6660)Termination reason: Time limit
% 11.99/1.90  
% 11.99/1.90  % (6660)Memory used [KB]: 4733
% 11.99/1.90  % (6660)Time elapsed: 0.519 s
% 11.99/1.90  % (6660)------------------------------
% 11.99/1.90  % (6660)------------------------------
% 11.99/1.90  % (6621)Time limit reached!
% 11.99/1.90  % (6621)------------------------------
% 11.99/1.90  % (6621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.99/1.90  % (6621)Termination reason: Time limit
% 11.99/1.90  % (6621)Termination phase: Saturation
% 11.99/1.90  
% 11.99/1.90  % (6621)Memory used [KB]: 18166
% 11.99/1.90  % (6621)Time elapsed: 1.500 s
% 11.99/1.90  % (6621)------------------------------
% 11.99/1.90  % (6621)------------------------------
% 11.99/1.91  % (6644)Time limit reached!
% 11.99/1.91  % (6644)------------------------------
% 11.99/1.91  % (6644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.99/1.91  % (6644)Termination reason: Time limit
% 11.99/1.91  
% 11.99/1.91  % (6644)Memory used [KB]: 17014
% 11.99/1.91  % (6644)Time elapsed: 1.509 s
% 11.99/1.91  % (6644)------------------------------
% 11.99/1.91  % (6644)------------------------------
% 11.99/1.95  % (6665)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.53/2.03  % (6667)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.53/2.03  % (6666)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.53/2.04  % (6668)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 12.53/2.04  % (6628)Time limit reached!
% 12.53/2.04  % (6628)------------------------------
% 12.53/2.04  % (6628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/2.04  % (6628)Termination reason: Time limit
% 12.53/2.04  
% 12.53/2.04  % (6628)Memory used [KB]: 20724
% 12.53/2.04  % (6628)Time elapsed: 1.646 s
% 12.53/2.04  % (6628)------------------------------
% 12.53/2.04  % (6628)------------------------------
% 13.99/2.18  % (6669)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.99/2.18  % (6654)Time limit reached!
% 13.99/2.18  % (6654)------------------------------
% 13.99/2.18  % (6654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.99/2.18  % (6654)Termination reason: Time limit
% 13.99/2.18  % (6654)Termination phase: Saturation
% 13.99/2.18  
% 13.99/2.18  % (6654)Memory used [KB]: 10234
% 13.99/2.18  % (6654)Time elapsed: 1.200 s
% 13.99/2.18  % (6654)------------------------------
% 13.99/2.18  % (6654)------------------------------
% 13.99/2.19  % (6664)Time limit reached!
% 13.99/2.19  % (6664)------------------------------
% 13.99/2.19  % (6664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.99/2.20  % (6664)Termination reason: Time limit
% 13.99/2.20  
% 13.99/2.20  % (6664)Memory used [KB]: 4733
% 13.99/2.20  % (6664)Time elapsed: 0.416 s
% 13.99/2.20  % (6664)------------------------------
% 13.99/2.20  % (6664)------------------------------
% 14.63/2.27  % (6631)Refutation found. Thanks to Tanya!
% 14.63/2.27  % SZS status Theorem for theBenchmark
% 14.63/2.28  % SZS output start Proof for theBenchmark
% 14.63/2.28  fof(f10391,plain,(
% 14.63/2.28    $false),
% 14.63/2.28    inference(avatar_sat_refutation,[],[f91,f96,f120,f128,f129,f136,f141,f186,f444,f562,f575,f584,f593,f598,f612,f704,f737,f739,f786,f788,f794,f822,f823,f824,f827,f834,f835,f836,f845,f1106,f1111,f1116,f1140,f1145,f1151,f1162,f1742,f1747,f1751,f1771,f1776,f1777,f1782,f1817,f1831,f1834,f2277,f2304,f2323,f2328,f2348,f2353,f2358,f2363,f7347,f7356,f7365,f7374,f7380,f10174,f10350,f10357,f10370,f10376,f10382,f10388,f10390])).
% 14.63/2.28  fof(f10390,plain,(
% 14.63/2.28    spl4_46 | ~spl4_48),
% 14.63/2.28    inference(avatar_contradiction_clause,[],[f10389])).
% 14.63/2.28  fof(f10389,plain,(
% 14.63/2.28    $false | (spl4_46 | ~spl4_48)),
% 14.63/2.28    inference(subsumption_resolution,[],[f10363,f1586])).
% 14.63/2.28  fof(f1586,plain,(
% 14.63/2.28    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X8,X9),X9) = X8) )),
% 14.63/2.28    inference(superposition,[],[f1566,f1429])).
% 14.63/2.28  fof(f1429,plain,(
% 14.63/2.28    ( ! [X2,X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X2)) = X2) )),
% 14.63/2.28    inference(backward_demodulation,[],[f755,f1411])).
% 14.63/2.28  fof(f1411,plain,(
% 14.63/2.28    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 14.63/2.28    inference(backward_demodulation,[],[f947,f1407])).
% 14.63/2.28  fof(f1407,plain,(
% 14.63/2.28    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.63/2.28    inference(forward_demodulation,[],[f1406,f724])).
% 14.63/2.28  fof(f724,plain,(
% 14.63/2.28    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 14.63/2.28    inference(backward_demodulation,[],[f387,f709])).
% 14.63/2.28  fof(f709,plain,(
% 14.63/2.28    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))) )),
% 14.63/2.28    inference(unit_resulting_resolution,[],[f313,f698])).
% 14.63/2.28  fof(f698,plain,(
% 14.63/2.28    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 14.63/2.28    inference(superposition,[],[f67,f64])).
% 14.63/2.28  fof(f64,plain,(
% 14.63/2.28    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 14.63/2.28    inference(definition_unfolding,[],[f28,f61])).
% 14.63/2.29  % (6670)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.23/2.29  fof(f61,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 15.23/2.29    inference(definition_unfolding,[],[f31,f60])).
% 15.23/2.29  fof(f60,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f32,f59])).
% 15.23/2.29  fof(f59,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f47,f58])).
% 15.23/2.29  fof(f58,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f14])).
% 15.23/2.29  fof(f14,axiom,(
% 15.23/2.29    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 15.23/2.29  fof(f47,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f13])).
% 15.23/2.29  fof(f13,axiom,(
% 15.23/2.29    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 15.23/2.29  fof(f32,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f12])).
% 15.23/2.29  fof(f12,axiom,(
% 15.23/2.29    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 15.23/2.29  fof(f31,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f17])).
% 15.23/2.29  fof(f17,axiom,(
% 15.23/2.29    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 15.23/2.29  fof(f28,plain,(
% 15.23/2.29    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.23/2.29    inference(cnf_transformation,[],[f7])).
% 15.23/2.29  fof(f7,axiom,(
% 15.23/2.29    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 15.23/2.29  fof(f67,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f36,f61])).
% 15.23/2.29  fof(f36,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 15.23/2.29    inference(cnf_transformation,[],[f24])).
% 15.23/2.29  fof(f24,plain,(
% 15.23/2.29    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.23/2.29    inference(ennf_transformation,[],[f6])).
% 15.23/2.29  fof(f6,axiom,(
% 15.23/2.29    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 15.23/2.29  fof(f313,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))),X2)) )),
% 15.23/2.29    inference(superposition,[],[f225,f176])).
% 15.23/2.29  fof(f176,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1)) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f162,f162,f39])).
% 15.23/2.29  fof(f39,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 15.23/2.29    inference(cnf_transformation,[],[f4])).
% 15.23/2.29  fof(f4,axiom,(
% 15.23/2.29    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 15.23/2.29  fof(f162,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f161,f41])).
% 15.23/2.29  fof(f41,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f25])).
% 15.23/2.29  fof(f25,plain,(
% 15.23/2.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.23/2.29    inference(ennf_transformation,[],[f1])).
% 15.23/2.29  fof(f1,axiom,(
% 15.23/2.29    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 15.23/2.29  fof(f161,plain,(
% 15.23/2.29    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3))) )),
% 15.23/2.29    inference(subsumption_resolution,[],[f157,f110])).
% 15.23/2.29  fof(f110,plain,(
% 15.23/2.29    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | ~r2_hidden(X4,X3)) )),
% 15.23/2.29    inference(superposition,[],[f84,f97])).
% 15.23/2.29  fof(f97,plain,(
% 15.23/2.29    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f81,f35])).
% 15.23/2.29  fof(f35,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f23])).
% 15.23/2.29  fof(f23,plain,(
% 15.23/2.29    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.23/2.29    inference(ennf_transformation,[],[f8])).
% 15.23/2.29  fof(f8,axiom,(
% 15.23/2.29    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 15.23/2.29  fof(f81,plain,(
% 15.23/2.29    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.23/2.29    inference(equality_resolution,[],[f38])).
% 15.23/2.29  fof(f38,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.23/2.29    inference(cnf_transformation,[],[f4])).
% 15.23/2.29  fof(f84,plain,(
% 15.23/2.29    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 15.23/2.29    inference(equality_resolution,[],[f73])).
% 15.23/2.29  fof(f73,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 15.23/2.29    inference(definition_unfolding,[],[f53,f33])).
% 15.23/2.29  fof(f33,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f5])).
% 15.23/2.29  fof(f5,axiom,(
% 15.23/2.29    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 15.23/2.29  fof(f53,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.23/2.29    inference(cnf_transformation,[],[f2])).
% 15.23/2.29  fof(f2,axiom,(
% 15.23/2.29    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 15.23/2.29  fof(f157,plain,(
% 15.23/2.29    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | r2_hidden(X4,X3)) )),
% 15.23/2.29    inference(superposition,[],[f85,f97])).
% 15.23/2.29  fof(f85,plain,(
% 15.23/2.29    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 15.23/2.29    inference(equality_resolution,[],[f74])).
% 15.23/2.29  fof(f74,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 15.23/2.29    inference(definition_unfolding,[],[f52,f33])).
% 15.23/2.29  fof(f52,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.23/2.29    inference(cnf_transformation,[],[f2])).
% 15.23/2.29  fof(f225,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),X1)) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f181,f41])).
% 15.23/2.29  fof(f181,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1))))) )),
% 15.23/2.29    inference(backward_demodulation,[],[f169,f177])).
% 15.23/2.29  fof(f177,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1)) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f162,f35])).
% 15.23/2.29  fof(f169,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X1),X2))))) )),
% 15.23/2.29    inference(forward_demodulation,[],[f163,f48])).
% 15.23/2.29  fof(f48,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f9])).
% 15.23/2.29  fof(f9,axiom,(
% 15.23/2.29    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 15.23/2.29  fof(f163,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(k5_xboole_0(X1,X1),X2)))) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f161,f85])).
% 15.23/2.29  fof(f387,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X0) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X2)))) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f162,f313,f39])).
% 15.23/2.29  fof(f1406,plain,(
% 15.23/2.29    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 15.23/2.29    inference(forward_demodulation,[],[f1384,f750])).
% 15.23/2.29  fof(f750,plain,(
% 15.23/2.29    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 15.23/2.29    inference(backward_demodulation,[],[f177,f724])).
% 15.23/2.29  fof(f1384,plain,(
% 15.23/2.29    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 15.23/2.29    inference(superposition,[],[f66,f64])).
% 15.23/2.29  fof(f66,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 15.23/2.29    inference(definition_unfolding,[],[f34,f61,f33])).
% 15.23/2.29  fof(f34,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f10])).
% 15.23/2.29  fof(f10,axiom,(
% 15.23/2.29    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 15.23/2.29  fof(f947,plain,(
% 15.23/2.29    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0)) )),
% 15.23/2.29    inference(superposition,[],[f755,f724])).
% 15.23/2.29  fof(f755,plain,(
% 15.23/2.29    ( ! [X2,X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X2)) = k5_xboole_0(k1_xboole_0,X2)) )),
% 15.23/2.29    inference(backward_demodulation,[],[f239,f724])).
% 15.23/2.29  fof(f239,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X2)) = k5_xboole_0(k5_xboole_0(X1,X1),X2)) )),
% 15.23/2.29    inference(superposition,[],[f48,f176])).
% 15.23/2.29  fof(f1566,plain,(
% 15.23/2.29    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) )),
% 15.23/2.29    inference(forward_demodulation,[],[f1549,f1407])).
% 15.23/2.29  fof(f1549,plain,(
% 15.23/2.29    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 15.23/2.29    inference(superposition,[],[f1429,f756])).
% 15.23/2.29  fof(f756,plain,(
% 15.23/2.29    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 15.23/2.29    inference(backward_demodulation,[],[f242,f724])).
% 15.23/2.29  fof(f242,plain,(
% 15.23/2.29    ( ! [X4,X5,X3] : (k5_xboole_0(X5,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 15.23/2.29    inference(superposition,[],[f48,f176])).
% 15.23/2.29  fof(f10363,plain,(
% 15.23/2.29    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (spl4_46 | ~spl4_48)),
% 15.23/2.29    inference(backward_demodulation,[],[f7379,f10349])).
% 15.23/2.29  fof(f10349,plain,(
% 15.23/2.29    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_48),
% 15.23/2.29    inference(avatar_component_clause,[],[f10347])).
% 15.23/2.29  fof(f10347,plain,(
% 15.23/2.29    spl4_48 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 15.23/2.29  fof(f7379,plain,(
% 15.23/2.29    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_46),
% 15.23/2.29    inference(avatar_component_clause,[],[f7377])).
% 15.23/2.29  fof(f7377,plain,(
% 15.23/2.29    spl4_46 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 15.23/2.29  fof(f10388,plain,(
% 15.23/2.29    ~spl4_53 | spl4_45 | ~spl4_48),
% 15.23/2.29    inference(avatar_split_clause,[],[f10383,f10347,f7371,f10385])).
% 15.23/2.29  fof(f10385,plain,(
% 15.23/2.29    spl4_53 <=> r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 15.23/2.29  fof(f7371,plain,(
% 15.23/2.29    spl4_45 <=> r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 15.23/2.29  fof(f10383,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl4_45 | ~spl4_48)),
% 15.23/2.29    inference(forward_demodulation,[],[f10362,f1429])).
% 15.23/2.29  fof(f10362,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl4_45 | ~spl4_48)),
% 15.23/2.29    inference(backward_demodulation,[],[f7373,f10349])).
% 15.23/2.29  fof(f7373,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_45),
% 15.23/2.29    inference(avatar_component_clause,[],[f7371])).
% 15.23/2.29  fof(f10382,plain,(
% 15.23/2.29    spl4_52 | ~spl4_44 | ~spl4_48),
% 15.23/2.29    inference(avatar_split_clause,[],[f10377,f10347,f7362,f10379])).
% 15.23/2.29  fof(f10379,plain,(
% 15.23/2.29    spl4_52 <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 15.23/2.29  fof(f7362,plain,(
% 15.23/2.29    spl4_44 <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 15.23/2.29  fof(f10377,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))) | (~spl4_44 | ~spl4_48)),
% 15.23/2.29    inference(forward_demodulation,[],[f10361,f1429])).
% 15.23/2.29  fof(f10361,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))) | (~spl4_44 | ~spl4_48)),
% 15.23/2.29    inference(backward_demodulation,[],[f7364,f10349])).
% 15.23/2.29  fof(f7364,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))) | ~spl4_44),
% 15.23/2.29    inference(avatar_component_clause,[],[f7362])).
% 15.23/2.29  fof(f10376,plain,(
% 15.23/2.29    ~spl4_51 | spl4_43 | ~spl4_48),
% 15.23/2.29    inference(avatar_split_clause,[],[f10371,f10347,f7353,f10373])).
% 15.23/2.29  fof(f10373,plain,(
% 15.23/2.29    spl4_51 <=> r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 15.23/2.29  fof(f7353,plain,(
% 15.23/2.29    spl4_43 <=> r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 15.23/2.29  fof(f10371,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) | (spl4_43 | ~spl4_48)),
% 15.23/2.29    inference(forward_demodulation,[],[f10360,f1429])).
% 15.23/2.29  fof(f10360,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))) | (spl4_43 | ~spl4_48)),
% 15.23/2.29    inference(backward_demodulation,[],[f7355,f10349])).
% 15.23/2.29  fof(f7355,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) | spl4_43),
% 15.23/2.29    inference(avatar_component_clause,[],[f7353])).
% 15.23/2.29  fof(f10370,plain,(
% 15.23/2.29    spl4_50 | ~spl4_42 | ~spl4_48),
% 15.23/2.29    inference(avatar_split_clause,[],[f10365,f10347,f7344,f10367])).
% 15.23/2.29  fof(f10367,plain,(
% 15.23/2.29    spl4_50 <=> r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 15.23/2.29  fof(f7344,plain,(
% 15.23/2.29    spl4_42 <=> r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 15.23/2.29  fof(f10365,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) | (~spl4_42 | ~spl4_48)),
% 15.23/2.29    inference(forward_demodulation,[],[f10359,f1429])).
% 15.23/2.29  fof(f10359,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))) | (~spl4_42 | ~spl4_48)),
% 15.23/2.29    inference(backward_demodulation,[],[f7346,f10349])).
% 15.23/2.29  fof(f7346,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))) | ~spl4_42),
% 15.23/2.29    inference(avatar_component_clause,[],[f7344])).
% 15.23/2.29  fof(f10357,plain,(
% 15.23/2.29    ~spl4_49 | spl4_1 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f10352,f559,f88,f10354])).
% 15.23/2.29  fof(f10354,plain,(
% 15.23/2.29    spl4_49 <=> sK1 = k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 15.23/2.29  fof(f88,plain,(
% 15.23/2.29    spl4_1 <=> sK1 = k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 15.23/2.29  fof(f559,plain,(
% 15.23/2.29    spl4_9 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 15.23/2.29  fof(f10352,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl4_1 | ~spl4_9)),
% 15.23/2.29    inference(subsumption_resolution,[],[f10344,f561])).
% 15.23/2.29  fof(f561,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_9),
% 15.23/2.29    inference(avatar_component_clause,[],[f559])).
% 15.23/2.29  fof(f10344,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 15.23/2.29    inference(superposition,[],[f90,f10193])).
% 15.23/2.29  fof(f10193,plain,(
% 15.23/2.29    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 15.23/2.29    inference(forward_demodulation,[],[f10192,f1566])).
% 15.23/2.29  fof(f10192,plain,(
% 15.23/2.29    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = k3_xboole_0(X3,X2) | ~r1_tarski(X2,X3)) )),
% 15.23/2.29    inference(forward_demodulation,[],[f10088,f1592])).
% 15.23/2.29  fof(f1592,plain,(
% 15.23/2.29    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 15.23/2.29    inference(superposition,[],[f1429,f1566])).
% 15.23/2.29  fof(f10088,plain,(
% 15.23/2.29    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k5_xboole_0(k5_xboole_0(X2,X3),X3) | ~r1_tarski(X2,X3)) )),
% 15.23/2.29    inference(superposition,[],[f1431,f1386])).
% 15.23/2.29  fof(f1386,plain,(
% 15.23/2.29    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5 | ~r1_tarski(X4,X5)) )),
% 15.23/2.29    inference(superposition,[],[f66,f67])).
% 15.23/2.29  fof(f1431,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) )),
% 15.23/2.29    inference(backward_demodulation,[],[f946,f1411])).
% 15.23/2.29  fof(f946,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) )),
% 15.23/2.29    inference(superposition,[],[f755,f48])).
% 15.23/2.29  fof(f90,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_1),
% 15.23/2.29    inference(avatar_component_clause,[],[f88])).
% 15.23/2.29  fof(f10350,plain,(
% 15.23/2.29    spl4_48 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f10313,f559,f10347])).
% 15.23/2.29  fof(f10313,plain,(
% 15.23/2.29    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_9),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f561,f10193])).
% 15.23/2.29  fof(f10174,plain,(
% 15.23/2.29    spl4_47 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f10060,f559,f10171])).
% 15.23/2.29  fof(f10171,plain,(
% 15.23/2.29    spl4_47 <=> sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 15.23/2.29  fof(f10060,plain,(
% 15.23/2.29    sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~spl4_9),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f561,f1386])).
% 15.23/2.29  fof(f7380,plain,(
% 15.23/2.29    ~spl4_46 | spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f7375,f88,f7377])).
% 15.23/2.29  fof(f7375,plain,(
% 15.23/2.29    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7336,f3144])).
% 15.23/2.29  fof(f3144,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))))) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f86,f71])).
% 15.23/2.29  fof(f71,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) | r2_hidden(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f45,f62,f33,f62])).
% 15.23/2.29  fof(f62,plain,(
% 15.23/2.29    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f29,f60])).
% 15.23/2.29  fof(f29,plain,(
% 15.23/2.29    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f11])).
% 15.23/2.29  fof(f11,axiom,(
% 15.23/2.29    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 15.23/2.29  fof(f45,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f16])).
% 15.23/2.29  fof(f16,axiom,(
% 15.23/2.29    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 15.23/2.29  fof(f86,plain,(
% 15.23/2.29    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 15.23/2.29    inference(equality_resolution,[],[f79])).
% 15.23/2.29  fof(f79,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 15.23/2.29    inference(definition_unfolding,[],[f56,f33,f62])).
% 15.23/2.29  fof(f56,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f18])).
% 15.23/2.29  fof(f18,axiom,(
% 15.23/2.29    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 15.23/2.29  fof(f7336,plain,(
% 15.23/2.29    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) | spl4_1),
% 15.23/2.29    inference(superposition,[],[f90,f66])).
% 15.23/2.29  fof(f7374,plain,(
% 15.23/2.29    ~spl4_45 | spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f7369,f88,f7371])).
% 15.23/2.29  fof(f7369,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7368,f3573])).
% 15.23/2.29  fof(f3573,plain,(
% 15.23/2.29    ( ! [X70,X71,X69] : (k5_xboole_0(X71,k5_xboole_0(X69,X70)) = k5_xboole_0(X71,k5_xboole_0(X70,X69))) )),
% 15.23/2.29    inference(forward_demodulation,[],[f3483,f1411])).
% 15.23/2.29  fof(f3483,plain,(
% 15.23/2.29    ( ! [X70,X71,X69] : (k5_xboole_0(X71,k5_xboole_0(X69,X70)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X71),k5_xboole_0(X70,X69))) )),
% 15.23/2.29    inference(superposition,[],[f1622,f2667])).
% 15.23/2.29  fof(f2667,plain,(
% 15.23/2.29    ( ! [X19,X18] : (k5_xboole_0(X19,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,X19))) )),
% 15.23/2.29    inference(superposition,[],[f2404,f724])).
% 15.23/2.29  fof(f2404,plain,(
% 15.23/2.29    ( ! [X35,X33,X34] : (k5_xboole_0(X34,X33) = k5_xboole_0(k5_xboole_0(X35,X33),k5_xboole_0(X35,X34))) )),
% 15.23/2.29    inference(superposition,[],[f1431,f1566])).
% 15.23/2.29  fof(f1622,plain,(
% 15.23/2.29    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10))) )),
% 15.23/2.29    inference(superposition,[],[f48,f1585])).
% 15.23/2.29  fof(f1585,plain,(
% 15.23/2.29    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6) )),
% 15.23/2.29    inference(superposition,[],[f1566,f1566])).
% 15.23/2.29  fof(f7368,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7367,f2587])).
% 15.23/2.29  fof(f2587,plain,(
% 15.23/2.29    ( ! [X43,X41,X42,X40] : (k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X40,X42))) = k5_xboole_0(X40,k5_xboole_0(X43,k5_xboole_0(X41,X42)))) )),
% 15.23/2.29    inference(superposition,[],[f1607,f1607])).
% 15.23/2.29  fof(f1607,plain,(
% 15.23/2.29    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X8,X10)))) )),
% 15.23/2.29    inference(forward_demodulation,[],[f1595,f48])).
% 15.23/2.29  fof(f1595,plain,(
% 15.23/2.29    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,X8),X10))) )),
% 15.23/2.29    inference(superposition,[],[f48,f1566])).
% 15.23/2.29  fof(f7367,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7366,f1653])).
% 15.23/2.29  fof(f1653,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))) )),
% 15.23/2.29    inference(superposition,[],[f1592,f48])).
% 15.23/2.29  fof(f7366,plain,(
% 15.23/2.29    ~r2_hidden(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7328,f66])).
% 15.23/2.29  fof(f7328,plain,(
% 15.23/2.29    ~r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_1),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f90,f1750])).
% 15.23/2.29  fof(f1750,plain,(
% 15.23/2.29    ( ! [X4,X3] : (~r2_hidden(X4,k3_enumset1(X3,X3,X3,X3,X3)) | X3 = X4) )),
% 15.23/2.29    inference(subsumption_resolution,[],[f1733,f1729])).
% 15.23/2.29  fof(f1729,plain,(
% 15.23/2.29    ( ! [X6,X7,X5] : (X5 = X6 | ~r2_hidden(X5,X7) | ~r2_hidden(X5,k3_enumset1(X6,X6,X6,X6,X6))) )),
% 15.23/2.29    inference(resolution,[],[f78,f84])).
% 15.23/2.29  fof(f78,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f57,f33,f62])).
% 15.23/2.29  fof(f57,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.23/2.29    inference(cnf_transformation,[],[f18])).
% 15.23/2.29  fof(f1733,plain,(
% 15.23/2.29    ( ! [X4,X3] : (r2_hidden(X4,k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X3,X3,X3,X3,X3))) | X3 = X4 | ~r2_hidden(X4,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 15.23/2.29    inference(superposition,[],[f78,f97])).
% 15.23/2.29  fof(f7365,plain,(
% 15.23/2.29    spl4_44 | spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f7360,f88,f7362])).
% 15.23/2.29  fof(f7360,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7359,f3573])).
% 15.23/2.29  fof(f7359,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7358,f2587])).
% 15.23/2.29  fof(f7358,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7357,f1653])).
% 15.23/2.29  fof(f7357,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7329,f66])).
% 15.23/2.29  fof(f7329,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))) | spl4_1),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f438,f90,f78])).
% 15.23/2.29  fof(f438,plain,(
% 15.23/2.29    ( ! [X0] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f81,f68])).
% 15.23/2.29  fof(f68,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f44,f62])).
% 15.23/2.29  fof(f44,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f15])).
% 15.23/2.29  fof(f15,axiom,(
% 15.23/2.29    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 15.23/2.29  fof(f7356,plain,(
% 15.23/2.29    ~spl4_43 | spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f7351,f88,f7353])).
% 15.23/2.29  fof(f7351,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7350,f3573])).
% 15.23/2.29  fof(f7350,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7349,f2587])).
% 15.23/2.29  fof(f7349,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7348,f1653])).
% 15.23/2.29  fof(f7348,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7330,f66])).
% 15.23/2.29  fof(f7330,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) | spl4_1),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f90,f1750])).
% 15.23/2.29  fof(f7347,plain,(
% 15.23/2.29    spl4_42 | spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f7342,f88,f7344])).
% 15.23/2.29  fof(f7342,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7341,f3573])).
% 15.23/2.29  fof(f7341,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7340,f2587])).
% 15.23/2.29  fof(f7340,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7339,f1653])).
% 15.23/2.29  fof(f7339,plain,(
% 15.23/2.29    r2_hidden(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7338,f66])).
% 15.23/2.29  fof(f7338,plain,(
% 15.23/2.29    r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))))) | spl4_1),
% 15.23/2.29    inference(forward_demodulation,[],[f7331,f1550])).
% 15.23/2.29  fof(f1550,plain,(
% 15.23/2.29    ( ! [X6,X7] : (k5_xboole_0(X7,k3_xboole_0(X7,X6)) = k5_xboole_0(X6,k3_tarski(k3_enumset1(X6,X6,X6,X6,X7)))) )),
% 15.23/2.29    inference(superposition,[],[f1429,f66])).
% 15.23/2.29  fof(f7331,plain,(
% 15.23/2.29    r2_hidden(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k3_enumset1(k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | spl4_1),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f438,f90,f78])).
% 15.23/2.29  fof(f2363,plain,(
% 15.23/2.29    ~spl4_41 | ~spl4_19),
% 15.23/2.29    inference(avatar_split_clause,[],[f2331,f791,f2360])).
% 15.23/2.29  fof(f2360,plain,(
% 15.23/2.29    spl4_41 <=> k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 15.23/2.29  fof(f791,plain,(
% 15.23/2.29    spl4_19 <=> r2_hidden(sK2(sK1,k1_xboole_0),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 15.23/2.29  fof(f2331,plain,(
% 15.23/2.29    k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)) != k5_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1)) | ~spl4_19),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f793,f70])).
% 15.23/2.29  fof(f70,plain,(
% 15.23/2.29    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f46,f62,f33,f62])).
% 15.23/2.29  fof(f46,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f16])).
% 15.23/2.29  fof(f793,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | ~spl4_19),
% 15.23/2.29    inference(avatar_component_clause,[],[f791])).
% 15.23/2.29  fof(f2358,plain,(
% 15.23/2.29    ~spl4_40 | ~spl4_13),
% 15.23/2.29    inference(avatar_split_clause,[],[f2332,f590,f2355])).
% 15.23/2.29  fof(f2355,plain,(
% 15.23/2.29    spl4_40 <=> k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 15.23/2.29  fof(f590,plain,(
% 15.23/2.29    spl4_13 <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 15.23/2.29  fof(f2332,plain,(
% 15.23/2.29    k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)) | ~spl4_13),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f592,f70])).
% 15.23/2.29  fof(f592,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | ~spl4_13),
% 15.23/2.29    inference(avatar_component_clause,[],[f590])).
% 15.23/2.29  fof(f2353,plain,(
% 15.23/2.29    ~spl4_39 | ~spl4_31),
% 15.23/2.29    inference(avatar_split_clause,[],[f2333,f1773,f2350])).
% 15.23/2.29  fof(f2350,plain,(
% 15.23/2.29    spl4_39 <=> k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)) = k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 15.23/2.29  fof(f1773,plain,(
% 15.23/2.29    spl4_31 <=> r2_hidden(sK2(sK1,sK1),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 15.23/2.29  fof(f2333,plain,(
% 15.23/2.29    k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)) != k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)) | ~spl4_31),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f1774,f70])).
% 15.23/2.29  fof(f1774,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,sK1),sK1) | ~spl4_31),
% 15.23/2.29    inference(avatar_component_clause,[],[f1773])).
% 15.23/2.29  fof(f2348,plain,(
% 15.23/2.29    ~spl4_38 | ~spl4_34),
% 15.23/2.29    inference(avatar_split_clause,[],[f2334,f2274,f2345])).
% 15.23/2.29  fof(f2345,plain,(
% 15.23/2.29    spl4_38 <=> k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 15.23/2.29  fof(f2274,plain,(
% 15.23/2.29    spl4_34 <=> r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 15.23/2.29  fof(f2334,plain,(
% 15.23/2.29    k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) != k5_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1)) | ~spl4_34),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f2276,f70])).
% 15.23/2.29  fof(f2276,plain,(
% 15.23/2.29    r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1) | ~spl4_34),
% 15.23/2.29    inference(avatar_component_clause,[],[f2274])).
% 15.23/2.29  fof(f2328,plain,(
% 15.23/2.29    ~spl4_37 | spl4_11),
% 15.23/2.29    inference(avatar_split_clause,[],[f2307,f577,f2325])).
% 15.23/2.29  fof(f2325,plain,(
% 15.23/2.29    spl4_37 <=> r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 15.23/2.29  fof(f577,plain,(
% 15.23/2.29    spl4_11 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 15.23/2.29  fof(f2307,plain,(
% 15.23/2.29    ~r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_11),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f578,f1750])).
% 15.23/2.29  fof(f578,plain,(
% 15.23/2.29    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl4_11),
% 15.23/2.29    inference(avatar_component_clause,[],[f577])).
% 15.23/2.29  fof(f2323,plain,(
% 15.23/2.29    ~spl4_36 | spl4_11),
% 15.23/2.29    inference(avatar_split_clause,[],[f2308,f577,f2320])).
% 15.23/2.29  fof(f2320,plain,(
% 15.23/2.29    spl4_36 <=> r2_hidden(sK1,k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 15.23/2.29  fof(f2308,plain,(
% 15.23/2.29    ~r2_hidden(sK1,k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_11),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f578,f1750])).
% 15.23/2.29  fof(f2304,plain,(
% 15.23/2.29    spl4_35 | ~spl4_34),
% 15.23/2.29    inference(avatar_split_clause,[],[f2294,f2274,f2301])).
% 15.23/2.29  fof(f2301,plain,(
% 15.23/2.29    spl4_35 <=> r1_tarski(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 15.23/2.29  fof(f2294,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),sK1) | ~spl4_34),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f2276,f69])).
% 15.23/2.29  fof(f69,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.23/2.29    inference(definition_unfolding,[],[f43,f62])).
% 15.23/2.29  fof(f43,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f15])).
% 15.23/2.29  fof(f2277,plain,(
% 15.23/2.29    spl4_34 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f2245,f559,f2274])).
% 15.23/2.29  fof(f2245,plain,(
% 15.23/2.29    r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),sK1) | ~spl4_9),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f811,f561,f104])).
% 15.23/2.29  fof(f104,plain,(
% 15.23/2.29    ( ! [X2,X3,X1] : (r2_hidden(sK2(X1,X2),X3) | ~r1_tarski(X1,X3) | r1_tarski(X1,X2)) )),
% 15.23/2.29    inference(resolution,[],[f40,f41])).
% 15.23/2.29  fof(f40,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f25])).
% 15.23/2.29  fof(f811,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0)) )),
% 15.23/2.29    inference(backward_demodulation,[],[f435,f756])).
% 15.23/2.29  fof(f435,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))))) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f248,f68])).
% 15.23/2.29  fof(f248,plain,(
% 15.23/2.29    ( ! [X12,X13,X11] : (~r2_hidden(X13,k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X12))))) )),
% 15.23/2.29    inference(superposition,[],[f161,f48])).
% 15.23/2.29  fof(f1834,plain,(
% 15.23/2.29    spl4_32 | ~spl4_31),
% 15.23/2.29    inference(avatar_split_clause,[],[f1823,f1773,f1779])).
% 15.23/2.29  fof(f1779,plain,(
% 15.23/2.29    spl4_32 <=> r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 15.23/2.29  fof(f1823,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1) | ~spl4_31),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f1774,f69])).
% 15.23/2.29  fof(f1831,plain,(
% 15.23/2.29    ~spl4_31 | spl4_32),
% 15.23/2.29    inference(avatar_contradiction_clause,[],[f1830])).
% 15.23/2.29  fof(f1830,plain,(
% 15.23/2.29    $false | (~spl4_31 | spl4_32)),
% 15.23/2.29    inference(subsumption_resolution,[],[f1823,f1780])).
% 15.23/2.29  fof(f1780,plain,(
% 15.23/2.29    ~r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1) | spl4_32),
% 15.23/2.29    inference(avatar_component_clause,[],[f1779])).
% 15.23/2.29  fof(f1817,plain,(
% 15.23/2.29    spl4_33 | spl4_31),
% 15.23/2.29    inference(avatar_split_clause,[],[f1812,f1773,f1814])).
% 15.23/2.29  fof(f1814,plain,(
% 15.23/2.29    spl4_33 <=> r2_hidden(sK2(sK1,sK1),k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 15.23/2.29  fof(f1812,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,sK1),k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)))))) | spl4_31),
% 15.23/2.29    inference(forward_demodulation,[],[f1805,f1550])).
% 15.23/2.29  fof(f1805,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,sK1),k5_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),k3_xboole_0(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1))) | spl4_31),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f438,f1775,f83])).
% 15.23/2.29  fof(f83,plain,(
% 15.23/2.29    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 15.23/2.29    inference(equality_resolution,[],[f72])).
% 15.23/2.29  fof(f72,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 15.23/2.29    inference(definition_unfolding,[],[f54,f33])).
% 15.23/2.29  fof(f54,plain,(
% 15.23/2.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.23/2.29    inference(cnf_transformation,[],[f2])).
% 15.23/2.29  fof(f1775,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,sK1),sK1) | spl4_31),
% 15.23/2.29    inference(avatar_component_clause,[],[f1773])).
% 15.23/2.29  fof(f1782,plain,(
% 15.23/2.29    spl4_32 | ~spl4_11 | ~spl4_15),
% 15.23/2.29    inference(avatar_split_clause,[],[f1759,f609,f577,f1779])).
% 15.23/2.29  fof(f609,plain,(
% 15.23/2.29    spl4_15 <=> r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 15.23/2.29  fof(f1759,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1),sK2(sK1,sK1)),sK1) | (~spl4_11 | ~spl4_15)),
% 15.23/2.29    inference(backward_demodulation,[],[f611,f579])).
% 15.23/2.29  fof(f579,plain,(
% 15.23/2.29    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl4_11),
% 15.23/2.29    inference(avatar_component_clause,[],[f577])).
% 15.23/2.29  fof(f611,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl4_15),
% 15.23/2.29    inference(avatar_component_clause,[],[f609])).
% 15.23/2.29  fof(f1777,plain,(
% 15.23/2.29    ~spl4_31 | ~spl4_11 | spl4_14),
% 15.23/2.29    inference(avatar_split_clause,[],[f1758,f595,f577,f1773])).
% 15.23/2.29  fof(f595,plain,(
% 15.23/2.29    spl4_14 <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 15.23/2.29  fof(f1758,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,sK1),sK1) | (~spl4_11 | spl4_14)),
% 15.23/2.29    inference(backward_demodulation,[],[f597,f579])).
% 15.23/2.29  fof(f597,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_14),
% 15.23/2.29    inference(avatar_component_clause,[],[f595])).
% 15.23/2.29  fof(f1776,plain,(
% 15.23/2.29    ~spl4_31 | ~spl4_11 | spl4_13),
% 15.23/2.29    inference(avatar_split_clause,[],[f1757,f590,f577,f1773])).
% 15.23/2.29  fof(f1757,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,sK1),sK1) | (~spl4_11 | spl4_13)),
% 15.23/2.29    inference(backward_demodulation,[],[f591,f579])).
% 15.23/2.29  fof(f591,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | spl4_13),
% 15.23/2.29    inference(avatar_component_clause,[],[f590])).
% 15.23/2.29  fof(f1771,plain,(
% 15.23/2.29    spl4_1 | ~spl4_11),
% 15.23/2.29    inference(avatar_contradiction_clause,[],[f1770])).
% 15.23/2.29  fof(f1770,plain,(
% 15.23/2.29    $false | (spl4_1 | ~spl4_11)),
% 15.23/2.29    inference(subsumption_resolution,[],[f1769,f815])).
% 15.23/2.29  fof(f815,plain,(
% 15.23/2.29    ( ! [X2] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2) )),
% 15.23/2.29    inference(backward_demodulation,[],[f695,f756])).
% 15.23/2.29  fof(f695,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),X2)) = X2) )),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f249,f67])).
% 15.23/2.29  fof(f249,plain,(
% 15.23/2.29    ( ! [X14,X15,X16] : (r1_tarski(k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X15))),X16)) )),
% 15.23/2.29    inference(superposition,[],[f162,f48])).
% 15.23/2.29  fof(f1769,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) | (spl4_1 | ~spl4_11)),
% 15.23/2.29    inference(forward_demodulation,[],[f1768,f724])).
% 15.23/2.29  fof(f1768,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1),sK1)) | (spl4_1 | ~spl4_11)),
% 15.23/2.29    inference(forward_demodulation,[],[f1752,f97])).
% 15.23/2.29  fof(f1752,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1)) | (spl4_1 | ~spl4_11)),
% 15.23/2.29    inference(backward_demodulation,[],[f90,f579])).
% 15.23/2.29  fof(f1751,plain,(
% 15.23/2.29    spl4_13 | ~spl4_23),
% 15.23/2.29    inference(avatar_split_clause,[],[f1515,f1108,f590])).
% 15.23/2.29  fof(f1108,plain,(
% 15.23/2.29    spl4_23 <=> r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 15.23/2.29  fof(f1515,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | ~spl4_23),
% 15.23/2.29    inference(backward_demodulation,[],[f1110,f1507])).
% 15.23/2.29  fof(f1507,plain,(
% 15.23/2.29    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2) )),
% 15.23/2.29    inference(forward_demodulation,[],[f1487,f815])).
% 15.23/2.29  fof(f1487,plain,(
% 15.23/2.29    ( ! [X2] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) )),
% 15.23/2.29    inference(superposition,[],[f1411,f66])).
% 15.23/2.29  fof(f1110,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_23),
% 15.23/2.29    inference(avatar_component_clause,[],[f1108])).
% 15.23/2.29  fof(f1747,plain,(
% 15.23/2.29    spl4_30 | spl4_11),
% 15.23/2.29    inference(avatar_split_clause,[],[f1720,f577,f1744])).
% 15.23/2.29  fof(f1744,plain,(
% 15.23/2.29    spl4_30 <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 15.23/2.29  fof(f1720,plain,(
% 15.23/2.29    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) | spl4_11),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f438,f578,f78])).
% 15.23/2.29  fof(f1742,plain,(
% 15.23/2.29    spl4_29 | spl4_11),
% 15.23/2.29    inference(avatar_split_clause,[],[f1737,f577,f1739])).
% 15.23/2.29  fof(f1739,plain,(
% 15.23/2.29    spl4_29 <=> r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 15.23/2.29  fof(f1737,plain,(
% 15.23/2.29    r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) | spl4_11),
% 15.23/2.29    inference(forward_demodulation,[],[f1721,f1550])).
% 15.23/2.29  fof(f1721,plain,(
% 15.23/2.29    r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | spl4_11),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f438,f578,f78])).
% 15.23/2.29  fof(f1162,plain,(
% 15.23/2.29    spl4_28 | spl4_25),
% 15.23/2.29    inference(avatar_split_clause,[],[f1156,f1137,f1159])).
% 15.23/2.29  fof(f1159,plain,(
% 15.23/2.29    spl4_28 <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 15.23/2.29  fof(f1137,plain,(
% 15.23/2.29    spl4_25 <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 15.23/2.29  fof(f1156,plain,(
% 15.23/2.29    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | spl4_25),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f1139,f41])).
% 15.23/2.29  fof(f1139,plain,(
% 15.23/2.29    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0) | spl4_25),
% 15.23/2.29    inference(avatar_component_clause,[],[f1137])).
% 15.23/2.29  fof(f1151,plain,(
% 15.23/2.29    spl4_27 | ~spl4_24),
% 15.23/2.29    inference(avatar_split_clause,[],[f1146,f1113,f1148])).
% 15.23/2.29  fof(f1148,plain,(
% 15.23/2.29    spl4_27 <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 15.23/2.29  fof(f1113,plain,(
% 15.23/2.29    spl4_24 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 15.23/2.29  fof(f1146,plain,(
% 15.23/2.29    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)))) | ~spl4_24),
% 15.23/2.29    inference(forward_demodulation,[],[f1122,f48])).
% 15.23/2.29  fof(f1122,plain,(
% 15.23/2.29    r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0))) | ~spl4_24),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f716,f1115,f83])).
% 15.23/2.29  fof(f1115,plain,(
% 15.23/2.29    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_24),
% 15.23/2.29    inference(avatar_component_clause,[],[f1113])).
% 15.23/2.29  fof(f716,plain,(
% 15.23/2.29    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 15.23/2.29    inference(backward_demodulation,[],[f181,f709])).
% 15.23/2.29  fof(f1145,plain,(
% 15.23/2.29    spl4_26 | ~spl4_24),
% 15.23/2.29    inference(avatar_split_clause,[],[f1125,f1113,f1142])).
% 15.23/2.29  fof(f1142,plain,(
% 15.23/2.29    spl4_26 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 15.23/2.29  fof(f1125,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_24),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f1115,f69])).
% 15.23/2.29  fof(f1140,plain,(
% 15.23/2.29    ~spl4_25 | ~spl4_24),
% 15.23/2.29    inference(avatar_split_clause,[],[f1130,f1113,f1137])).
% 15.23/2.29  fof(f1130,plain,(
% 15.23/2.29    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k1_xboole_0) | ~spl4_24),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f716,f1115,f40])).
% 15.23/2.29  fof(f1116,plain,(
% 15.23/2.29    spl4_24 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f1081,f93,f1113])).
% 15.23/2.29  fof(f93,plain,(
% 15.23/2.29    spl4_2 <=> r2_hidden(sK0,sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 15.23/2.29  fof(f1081,plain,(
% 15.23/2.29    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f95,f716,f83])).
% 15.23/2.29  fof(f95,plain,(
% 15.23/2.29    r2_hidden(sK0,sK1) | ~spl4_2),
% 15.23/2.29    inference(avatar_component_clause,[],[f93])).
% 15.23/2.29  fof(f1111,plain,(
% 15.23/2.29    spl4_23 | ~spl4_13),
% 15.23/2.29    inference(avatar_split_clause,[],[f1083,f590,f1108])).
% 15.23/2.29  fof(f1083,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_13),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f592,f716,f83])).
% 15.23/2.29  fof(f1106,plain,(
% 15.23/2.29    spl4_22 | ~spl4_19),
% 15.23/2.29    inference(avatar_split_clause,[],[f1084,f791,f1103])).
% 15.23/2.29  fof(f1103,plain,(
% 15.23/2.29    spl4_22 <=> r2_hidden(sK2(sK1,k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 15.23/2.29  fof(f1084,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | ~spl4_19),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f793,f716,f83])).
% 15.23/2.29  fof(f845,plain,(
% 15.23/2.29    spl4_19 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f731,f93,f791])).
% 15.23/2.29  fof(f731,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f479,f709])).
% 15.23/2.29  fof(f479,plain,(
% 15.23/2.29    ( ! [X0,X1] : (r2_hidden(sK2(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f358,f41])).
% 15.23/2.29  fof(f358,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r1_tarski(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))))) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f234,f103])).
% 15.23/2.29  fof(f103,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK0,X0)) ) | ~spl4_2),
% 15.23/2.29    inference(resolution,[],[f40,f95])).
% 15.23/2.29  fof(f234,plain,(
% 15.23/2.29    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X1))))) )),
% 15.23/2.29    inference(superposition,[],[f181,f176])).
% 15.23/2.29  fof(f836,plain,(
% 15.23/2.29    spl4_19 | ~spl4_5),
% 15.23/2.29    inference(avatar_split_clause,[],[f773,f133,f791])).
% 15.23/2.29  fof(f133,plain,(
% 15.23/2.29    spl4_5 <=> r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 15.23/2.29  fof(f773,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | ~spl4_5),
% 15.23/2.29    inference(backward_demodulation,[],[f135,f724])).
% 15.23/2.29  fof(f135,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1) | ~spl4_5),
% 15.23/2.29    inference(avatar_component_clause,[],[f133])).
% 15.23/2.29  fof(f835,plain,(
% 15.23/2.29    ~spl4_17 | spl4_4),
% 15.23/2.29    inference(avatar_split_clause,[],[f772,f125,f734])).
% 15.23/2.29  fof(f734,plain,(
% 15.23/2.29    spl4_17 <=> r1_tarski(sK1,k1_xboole_0)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 15.23/2.29  fof(f125,plain,(
% 15.23/2.29    spl4_4 <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 15.23/2.29  fof(f772,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | spl4_4),
% 15.23/2.29    inference(backward_demodulation,[],[f127,f724])).
% 15.23/2.29  fof(f127,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | spl4_4),
% 15.23/2.29    inference(avatar_component_clause,[],[f125])).
% 15.23/2.29  fof(f834,plain,(
% 15.23/2.29    spl4_21 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f765,f93,f831])).
% 15.23/2.29  fof(f831,plain,(
% 15.23/2.29    spl4_21 <=> r1_tarski(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 15.23/2.29  fof(f765,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0),sK2(sK1,k1_xboole_0)),sK1) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f550,f724])).
% 15.23/2.29  fof(f550,plain,(
% 15.23/2.29    ( ! [X0] : (r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0)),sK2(sK1,k5_xboole_0(X0,X0))),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f188,f69])).
% 15.23/2.29  fof(f188,plain,(
% 15.23/2.29    ( ! [X0] : (r2_hidden(sK2(sK1,k5_xboole_0(X0,X0)),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f167,f41])).
% 15.23/2.29  fof(f167,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,X0))) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f161,f103])).
% 15.23/2.29  fof(f827,plain,(
% 15.23/2.29    ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f826,f93,f734])).
% 15.23/2.29  fof(f826,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 15.23/2.29    inference(forward_demodulation,[],[f816,f724])).
% 15.23/2.29  fof(f816,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f795,f756])).
% 15.23/2.29  fof(f795,plain,(
% 15.23/2.29    ( ! [X6,X7] : (~r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(X6,X7)))))) ) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f482,f755])).
% 15.23/2.29  fof(f482,plain,(
% 15.23/2.29    ( ! [X6,X8,X7] : (~r1_tarski(sK1,k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(X6,X7))))))) ) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f358,f48])).
% 15.23/2.29  fof(f824,plain,(
% 15.23/2.29    spl4_19 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f805,f93,f791])).
% 15.23/2.29  fof(f805,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f254,f756])).
% 15.23/2.29  fof(f254,plain,(
% 15.23/2.29    ( ! [X28,X29] : (r2_hidden(sK2(sK1,k5_xboole_0(X28,k5_xboole_0(X29,k5_xboole_0(X28,X29)))),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f188,f48])).
% 15.23/2.29  fof(f823,plain,(
% 15.23/2.29    ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f804,f93,f734])).
% 15.23/2.29  fof(f804,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f250,f756])).
% 15.23/2.29  fof(f250,plain,(
% 15.23/2.29    ( ! [X17,X18] : (~r1_tarski(sK1,k5_xboole_0(X17,k5_xboole_0(X18,k5_xboole_0(X17,X18))))) ) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f167,f48])).
% 15.23/2.29  fof(f822,plain,(
% 15.23/2.29    spl4_20 | ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f800,f93,f734,f820])).
% 15.23/2.29  fof(f820,plain,(
% 15.23/2.29    spl4_20 <=> ! [X5,X6] : ~r1_tarski(k5_xboole_0(X5,X6),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 15.23/2.29  fof(f800,plain,(
% 15.23/2.29    ( ! [X6,X5] : (~r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(k5_xboole_0(X5,X6),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f246,f756])).
% 15.23/2.29  fof(f246,plain,(
% 15.23/2.29    ( ! [X6,X5] : (~r1_tarski(sK1,k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) | ~r1_tarski(k5_xboole_0(X5,X6),sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f144,f48])).
% 15.23/2.29  fof(f144,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f112,f35])).
% 15.23/2.29  fof(f112,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f95,f107,f40])).
% 15.23/2.29  fof(f107,plain,(
% 15.23/2.29    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f95,f84])).
% 15.23/2.29  fof(f794,plain,(
% 15.23/2.29    spl4_19 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f752,f93,f791])).
% 15.23/2.29  fof(f752,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f188,f724])).
% 15.23/2.29  fof(f788,plain,(
% 15.23/2.29    ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f748,f93,f734])).
% 15.23/2.29  fof(f748,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f167,f724])).
% 15.23/2.29  fof(f786,plain,(
% 15.23/2.29    spl4_18 | ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f743,f93,f734,f784])).
% 15.23/2.29  fof(f784,plain,(
% 15.23/2.29    spl4_18 <=> ! [X0] : ~r1_tarski(X0,sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 15.23/2.29  fof(f743,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(X0,sK1)) ) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f144,f724])).
% 15.23/2.29  fof(f739,plain,(
% 15.23/2.29    ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f723,f93,f734])).
% 15.23/2.29  fof(f723,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f358,f709])).
% 15.23/2.29  fof(f737,plain,(
% 15.23/2.29    ~spl4_17 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f718,f93,f734])).
% 15.23/2.29  fof(f718,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k1_xboole_0) | ~spl4_2),
% 15.23/2.29    inference(backward_demodulation,[],[f232,f709])).
% 15.23/2.29  fof(f232,plain,(
% 15.23/2.29    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))) ) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f181,f103])).
% 15.23/2.29  fof(f704,plain,(
% 15.23/2.29    spl4_16 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f697,f559,f701])).
% 15.23/2.29  fof(f701,plain,(
% 15.23/2.29    spl4_16 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 15.23/2.29  fof(f697,plain,(
% 15.23/2.29    sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl4_9),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f561,f67])).
% 15.23/2.29  fof(f612,plain,(
% 15.23/2.29    spl4_15 | ~spl4_13),
% 15.23/2.29    inference(avatar_split_clause,[],[f599,f590,f609])).
% 15.23/2.29  fof(f599,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl4_13),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f592,f69])).
% 15.23/2.29  fof(f598,plain,(
% 15.23/2.29    ~spl4_14 | spl4_12),
% 15.23/2.29    inference(avatar_split_clause,[],[f587,f581,f595])).
% 15.23/2.29  fof(f581,plain,(
% 15.23/2.29    spl4_12 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 15.23/2.29  fof(f587,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_12),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f583,f42])).
% 15.23/2.29  fof(f42,plain,(
% 15.23/2.29    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 15.23/2.29    inference(cnf_transformation,[],[f25])).
% 15.23/2.29  fof(f583,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_12),
% 15.23/2.29    inference(avatar_component_clause,[],[f581])).
% 15.23/2.29  fof(f593,plain,(
% 15.23/2.29    spl4_13 | spl4_12),
% 15.23/2.29    inference(avatar_split_clause,[],[f588,f581,f590])).
% 15.23/2.29  fof(f588,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | spl4_12),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f583,f41])).
% 15.23/2.29  fof(f584,plain,(
% 15.23/2.29    spl4_11 | ~spl4_12 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f570,f559,f581,f577])).
% 15.23/2.29  fof(f570,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl4_9),
% 15.23/2.29    inference(resolution,[],[f561,f39])).
% 15.23/2.29  fof(f575,plain,(
% 15.23/2.29    spl4_10 | ~spl4_9),
% 15.23/2.29    inference(avatar_split_clause,[],[f568,f559,f572])).
% 15.23/2.29  fof(f572,plain,(
% 15.23/2.29    spl4_10 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 15.23/2.29  fof(f568,plain,(
% 15.23/2.29    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_9),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f561,f35])).
% 15.23/2.29  fof(f562,plain,(
% 15.23/2.29    spl4_9 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f548,f93,f559])).
% 15.23/2.29  fof(f548,plain,(
% 15.23/2.29    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_2),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f95,f69])).
% 15.23/2.29  fof(f444,plain,(
% 15.23/2.29    ~spl4_8 | spl4_6),
% 15.23/2.29    inference(avatar_split_clause,[],[f437,f138,f441])).
% 15.23/2.29  fof(f441,plain,(
% 15.23/2.29    spl4_8 <=> r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1))),k5_xboole_0(sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 15.23/2.29  fof(f138,plain,(
% 15.23/2.29    spl4_6 <=> r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 15.23/2.29  fof(f437,plain,(
% 15.23/2.29    ~r1_tarski(k3_enumset1(sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1)),sK2(sK1,k5_xboole_0(sK1,sK1))),k5_xboole_0(sK1,sK1)) | spl4_6),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f140,f68])).
% 15.23/2.29  fof(f140,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl4_6),
% 15.23/2.29    inference(avatar_component_clause,[],[f138])).
% 15.23/2.29  fof(f186,plain,(
% 15.23/2.29    ~spl4_7 | spl4_3),
% 15.23/2.29    inference(avatar_split_clause,[],[f180,f117,f183])).
% 15.23/2.29  fof(f183,plain,(
% 15.23/2.29    spl4_7 <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 15.23/2.29  fof(f117,plain,(
% 15.23/2.29    spl4_3 <=> r2_hidden(sK0,k5_xboole_0(sK1,sK1))),
% 15.23/2.29    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 15.23/2.29  fof(f180,plain,(
% 15.23/2.29    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | spl4_3),
% 15.23/2.29    inference(backward_demodulation,[],[f158,f177])).
% 15.23/2.29  fof(f158,plain,(
% 15.23/2.29    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))) ) | spl4_3),
% 15.23/2.29    inference(forward_demodulation,[],[f154,f48])).
% 15.23/2.29  fof(f154,plain,(
% 15.23/2.29    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))) ) | spl4_3),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f119,f85])).
% 15.23/2.29  fof(f119,plain,(
% 15.23/2.29    ~r2_hidden(sK0,k5_xboole_0(sK1,sK1)) | spl4_3),
% 15.23/2.29    inference(avatar_component_clause,[],[f117])).
% 15.23/2.29  fof(f141,plain,(
% 15.23/2.29    ~spl4_6 | spl4_4),
% 15.23/2.29    inference(avatar_split_clause,[],[f130,f125,f138])).
% 15.23/2.29  fof(f130,plain,(
% 15.23/2.29    ~r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl4_4),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f127,f42])).
% 15.23/2.29  fof(f136,plain,(
% 15.23/2.29    spl4_5 | spl4_4),
% 15.23/2.29    inference(avatar_split_clause,[],[f131,f125,f133])).
% 15.23/2.29  fof(f131,plain,(
% 15.23/2.29    r2_hidden(sK2(sK1,k5_xboole_0(sK1,sK1)),sK1) | spl4_4),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f127,f41])).
% 15.23/2.29  fof(f129,plain,(
% 15.23/2.29    ~spl4_4 | ~spl4_2 | spl4_3),
% 15.23/2.29    inference(avatar_split_clause,[],[f121,f117,f93,f125])).
% 15.23/2.29  fof(f121,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl4_2 | spl4_3)),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f119,f103])).
% 15.23/2.29  fof(f128,plain,(
% 15.23/2.29    ~spl4_4 | ~spl4_2 | spl4_3),
% 15.23/2.29    inference(avatar_split_clause,[],[f122,f117,f93,f125])).
% 15.23/2.29  fof(f122,plain,(
% 15.23/2.29    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl4_2 | spl4_3)),
% 15.23/2.29    inference(unit_resulting_resolution,[],[f95,f119,f40])).
% 15.23/2.29  fof(f120,plain,(
% 15.23/2.29    ~spl4_3 | ~spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f115,f93,f117])).
% 15.23/2.29  fof(f115,plain,(
% 15.23/2.29    ~r2_hidden(sK0,k5_xboole_0(sK1,sK1)) | ~spl4_2),
% 15.23/2.29    inference(superposition,[],[f107,f97])).
% 15.23/2.29  fof(f96,plain,(
% 15.23/2.29    spl4_2),
% 15.23/2.29    inference(avatar_split_clause,[],[f26,f93])).
% 15.23/2.29  fof(f26,plain,(
% 15.23/2.29    r2_hidden(sK0,sK1)),
% 15.23/2.29    inference(cnf_transformation,[],[f22])).
% 15.23/2.29  fof(f22,plain,(
% 15.23/2.29    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 15.23/2.29    inference(ennf_transformation,[],[f20])).
% 15.23/2.29  fof(f20,negated_conjecture,(
% 15.23/2.29    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 15.23/2.29    inference(negated_conjecture,[],[f19])).
% 15.23/2.29  fof(f19,conjecture,(
% 15.23/2.29    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 15.23/2.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 15.23/2.29  fof(f91,plain,(
% 15.23/2.29    ~spl4_1),
% 15.23/2.29    inference(avatar_split_clause,[],[f63,f88])).
% 15.23/2.29  fof(f63,plain,(
% 15.23/2.29    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 15.23/2.29    inference(definition_unfolding,[],[f27,f61,f33,f62,f62])).
% 15.23/2.29  fof(f27,plain,(
% 15.23/2.29    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 15.23/2.29    inference(cnf_transformation,[],[f22])).
% 15.23/2.29  % SZS output end Proof for theBenchmark
% 15.23/2.29  % (6631)------------------------------
% 15.23/2.29  % (6631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.23/2.29  % (6631)Termination reason: Refutation
% 15.23/2.29  
% 15.23/2.29  % (6631)Memory used [KB]: 21236
% 15.23/2.29  % (6631)Time elapsed: 1.797 s
% 15.23/2.29  % (6631)------------------------------
% 15.23/2.29  % (6631)------------------------------
% 15.23/2.30  % (6616)Success in time 1.945 s
%------------------------------------------------------------------------------
