%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:00 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 314 expanded)
%              Number of leaves         :   40 ( 146 expanded)
%              Depth                    :    8
%              Number of atoms          :  372 ( 699 expanded)
%              Number of equality atoms :   35 ( 120 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f63,f67,f71,f78,f82,f90,f103,f113,f121,f195,f213,f217,f271,f402,f597,f669,f699,f725,f881,f1188,f1234,f1396,f1684,f1803,f1897,f2112,f2179])).

fof(f2179,plain,
    ( ~ spl6_138
    | ~ spl6_144
    | spl6_164 ),
    inference(avatar_contradiction_clause,[],[f2178])).

fof(f2178,plain,
    ( $false
    | ~ spl6_138
    | ~ spl6_144
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2111,f2161])).

fof(f2161,plain,
    ( ! [X47,X46] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X46)),k3_tarski(k1_enumset1(sK3,sK3,X47))))
    | ~ spl6_138
    | ~ spl6_144 ),
    inference(resolution,[],[f1896,f1802])).

fof(f1802,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7)
        | r1_tarski(sK0,X7) )
    | ~ spl6_138 ),
    inference(avatar_component_clause,[],[f1801])).

fof(f1801,plain,
    ( spl6_138
  <=> ! [X7,X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7)
        | r1_tarski(sK0,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).

fof(f1896,plain,
    ( ! [X43,X44,X42] : r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44))))
    | ~ spl6_144 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f1895,plain,
    ( spl6_144
  <=> ! [X42,X44,X43] : r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f2111,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_164 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f2109,plain,
    ( spl6_164
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).

fof(f2112,plain,
    ( ~ spl6_164
    | spl6_54
    | ~ spl6_97
    | ~ spl6_110
    | ~ spl6_133 ),
    inference(avatar_split_clause,[],[f1757,f1682,f1394,f1186,f594,f2109])).

fof(f594,plain,
    ( spl6_54
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f1186,plain,
    ( spl6_97
  <=> ! [X13,X12,X14] :
        ( r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12)
        | ~ r1_tarski(X14,X12)
        | ~ r1_tarski(X13,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f1394,plain,
    ( spl6_110
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f1682,plain,
    ( spl6_133
  <=> ! [X36,X35] : r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f1757,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_54
    | ~ spl6_97
    | ~ spl6_110
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1199,f1737])).

fof(f1737,plain,
    ( ! [X45,X44] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X44,X44,sK4)),k3_tarski(k1_enumset1(X45,X45,sK5))))
    | ~ spl6_110
    | ~ spl6_133 ),
    inference(superposition,[],[f1683,f1395])).

fof(f1395,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1683,plain,
    ( ! [X35,X36] : r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5))))))
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f1682])).

fof(f1199,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_54
    | ~ spl6_97 ),
    inference(resolution,[],[f1187,f596])).

fof(f596,plain,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f594])).

fof(f1187,plain,
    ( ! [X14,X12,X13] :
        ( r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12)
        | ~ r1_tarski(X14,X12)
        | ~ r1_tarski(X13,X12) )
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f1897,plain,
    ( spl6_144
    | ~ spl6_3
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1557,f1232,f61,f1895])).

fof(f61,plain,
    ( spl6_3
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1232,plain,
    ( spl6_100
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1557,plain,
    ( ! [X43,X44,X42] : r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44))))
    | ~ spl6_3
    | ~ spl6_100 ),
    inference(superposition,[],[f62,f1233])).

fof(f1233,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1232])).

fof(f62,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f1803,plain,
    ( spl6_138
    | ~ spl6_27
    | ~ spl6_110 ),
    inference(avatar_split_clause,[],[f1718,f1394,f269,f1801])).

fof(f269,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1)
        | r1_tarski(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1718,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7)
        | r1_tarski(sK0,X7) )
    | ~ spl6_27
    | ~ spl6_110 ),
    inference(superposition,[],[f270,f1395])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1)
        | r1_tarski(sK0,X1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1684,plain,
    ( spl6_133
    | ~ spl6_24
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1553,f1232,f215,f1682])).

fof(f215,plain,
    ( spl6_24
  <=> ! [X3,X2] : r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1553,plain,
    ( ! [X35,X36] : r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5))))))
    | ~ spl6_24
    | ~ spl6_100 ),
    inference(superposition,[],[f216,f1233])).

fof(f216,plain,
    ( ! [X2,X3] : r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5))))))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f215])).

fof(f1396,plain,(
    spl6_110 ),
    inference(avatar_split_clause,[],[f46,f1394])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f34,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f1234,plain,(
    spl6_100 ),
    inference(avatar_split_clause,[],[f45,f1232])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1188,plain,
    ( spl6_97
    | ~ spl6_64
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1073,f879,f723,f1186])).

fof(f723,plain,
    ( spl6_64
  <=> ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f879,plain,
    ( spl6_80
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f1073,plain,
    ( ! [X14,X12,X13] :
        ( r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12)
        | ~ r1_tarski(X14,X12)
        | ~ r1_tarski(X13,X12) )
    | ~ spl6_64
    | ~ spl6_80 ),
    inference(superposition,[],[f880,f724])).

fof(f724,plain,
    ( ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f723])).

fof(f880,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f879])).

fof(f881,plain,(
    spl6_80 ),
    inference(avatar_split_clause,[],[f49,f879])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f725,plain,
    ( spl6_64
    | ~ spl6_13
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f700,f697,f119,f723])).

fof(f119,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f697,plain,
    ( spl6_63
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f700,plain,
    ( ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0
    | ~ spl6_13
    | ~ spl6_63 ),
    inference(resolution,[],[f698,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f698,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f697])).

fof(f699,plain,
    ( spl6_63
    | ~ spl6_3
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f680,f667,f61,f697])).

fof(f667,plain,
    ( spl6_62
  <=> ! [X1,X0] : k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f680,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl6_3
    | ~ spl6_62 ),
    inference(superposition,[],[f62,f668])).

fof(f668,plain,
    ( ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f667])).

fof(f669,plain,
    ( spl6_62
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f406,f400,f119,f69,f667])).

fof(f69,plain,
    ( spl6_5
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f400,plain,
    ( spl6_37
  <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f406,plain,
    ( ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f403,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f403,plain,
    ( ! [X0,X1] : k3_tarski(k1_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(resolution,[],[f401,f120])).

fof(f401,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f400])).

fof(f597,plain,(
    ~ spl6_54 ),
    inference(avatar_split_clause,[],[f41,f594])).

fof(f41,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f27,f40,f40,f40])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f402,plain,
    ( spl6_37
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f375,f211,f88,f400])).

fof(f88,plain,
    ( spl6_8
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f211,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
        | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f375,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(resolution,[],[f212,f89])).

fof(f89,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
        | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f271,plain,
    ( spl6_27
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f122,f111,f65,f269])).

fof(f65,plain,
    ( spl6_4
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f111,plain,
    ( spl6_11
  <=> ! [X0] : r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1)
        | r1_tarski(sK0,X1) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(resolution,[],[f112,f66])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f112,plain,
    ( ! [X0] : r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f217,plain,
    ( spl6_24
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f202,f193,f88,f215])).

fof(f193,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1)
        | r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f202,plain,
    ( ! [X2,X3] : r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5))))))
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(resolution,[],[f194,f89])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f213,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f47,f211])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f36,f32,f40])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f195,plain,
    ( spl6_21
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f107,f101,f65,f193])).

fof(f101,plain,
    ( spl6_10
  <=> ! [X4] : r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f102,f66])).

fof(f102,plain,
    ( ! [X4] : r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f121,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f113,plain,
    ( spl6_11
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f83,f76,f61,f111])).

fof(f76,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f83,plain,
    ( ! [X0] : r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f77,f62])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f103,plain,
    ( spl6_10
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f93,f88,f80,f101])).

fof(f80,plain,
    ( spl6_7
  <=> ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f93,plain,
    ( ! [X4] : r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f90,plain,
    ( spl6_8
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f85,f69,f61,f88])).

fof(f85,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f62,f70])).

fof(f82,plain,
    ( spl6_7
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f73,f65,f56,f80])).

fof(f56,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f73,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f78,plain,
    ( spl6_6
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f72,f65,f51,f76])).

fof(f51,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f71,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f43,f69])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f67,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f65])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f63,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f42,f61])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1685)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (1676)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (1679)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (1683)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (1671)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (1686)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (1677)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (1675)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (1682)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (1678)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (1674)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (1673)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (1680)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (1687)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (1684)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (1681)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (1688)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (1689)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.88/0.61  % (1679)Refutation found. Thanks to Tanya!
% 1.88/0.61  % SZS status Theorem for theBenchmark
% 1.88/0.61  % SZS output start Proof for theBenchmark
% 1.88/0.61  fof(f2180,plain,(
% 1.88/0.61    $false),
% 1.88/0.61    inference(avatar_sat_refutation,[],[f54,f59,f63,f67,f71,f78,f82,f90,f103,f113,f121,f195,f213,f217,f271,f402,f597,f669,f699,f725,f881,f1188,f1234,f1396,f1684,f1803,f1897,f2112,f2179])).
% 1.88/0.61  fof(f2179,plain,(
% 1.88/0.61    ~spl6_138 | ~spl6_144 | spl6_164),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f2178])).
% 1.88/0.61  fof(f2178,plain,(
% 1.88/0.61    $false | (~spl6_138 | ~spl6_144 | spl6_164)),
% 1.88/0.61    inference(subsumption_resolution,[],[f2111,f2161])).
% 1.88/0.61  fof(f2161,plain,(
% 1.88/0.61    ( ! [X47,X46] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X46)),k3_tarski(k1_enumset1(sK3,sK3,X47))))) ) | (~spl6_138 | ~spl6_144)),
% 1.88/0.61    inference(resolution,[],[f1896,f1802])).
% 1.88/0.61  fof(f1802,plain,(
% 1.88/0.61    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7) | r1_tarski(sK0,X7)) ) | ~spl6_138),
% 1.88/0.61    inference(avatar_component_clause,[],[f1801])).
% 1.88/0.61  fof(f1801,plain,(
% 1.88/0.61    spl6_138 <=> ! [X7,X6] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7) | r1_tarski(sK0,X7))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).
% 1.88/0.61  fof(f1896,plain,(
% 1.88/0.61    ( ! [X43,X44,X42] : (r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44))))) ) | ~spl6_144),
% 1.88/0.61    inference(avatar_component_clause,[],[f1895])).
% 1.88/0.61  fof(f1895,plain,(
% 1.88/0.61    spl6_144 <=> ! [X42,X44,X43] : r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).
% 1.88/0.61  fof(f2111,plain,(
% 1.88/0.61    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_164),
% 1.88/0.61    inference(avatar_component_clause,[],[f2109])).
% 1.88/0.61  fof(f2109,plain,(
% 1.88/0.61    spl6_164 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).
% 1.88/0.61  fof(f2112,plain,(
% 1.88/0.61    ~spl6_164 | spl6_54 | ~spl6_97 | ~spl6_110 | ~spl6_133),
% 1.88/0.61    inference(avatar_split_clause,[],[f1757,f1682,f1394,f1186,f594,f2109])).
% 1.88/0.61  fof(f594,plain,(
% 1.88/0.61    spl6_54 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.88/0.61  fof(f1186,plain,(
% 1.88/0.61    spl6_97 <=> ! [X13,X12,X14] : (r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12) | ~r1_tarski(X14,X12) | ~r1_tarski(X13,X12))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 1.88/0.61  fof(f1394,plain,(
% 1.88/0.61    spl6_110 <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 1.88/0.61  fof(f1682,plain,(
% 1.88/0.61    spl6_133 <=> ! [X36,X35] : r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5))))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).
% 1.88/0.61  fof(f1757,plain,(
% 1.88/0.61    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | (spl6_54 | ~spl6_97 | ~spl6_110 | ~spl6_133)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1199,f1737])).
% 1.88/0.61  fof(f1737,plain,(
% 1.88/0.61    ( ! [X45,X44] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X44,X44,sK4)),k3_tarski(k1_enumset1(X45,X45,sK5))))) ) | (~spl6_110 | ~spl6_133)),
% 1.88/0.61    inference(superposition,[],[f1683,f1395])).
% 1.88/0.61  fof(f1395,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ) | ~spl6_110),
% 1.88/0.61    inference(avatar_component_clause,[],[f1394])).
% 1.88/0.61  fof(f1683,plain,(
% 1.88/0.61    ( ! [X35,X36] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5))))))) ) | ~spl6_133),
% 1.88/0.61    inference(avatar_component_clause,[],[f1682])).
% 1.88/0.61  fof(f1199,plain,(
% 1.88/0.61    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | (spl6_54 | ~spl6_97)),
% 1.88/0.61    inference(resolution,[],[f1187,f596])).
% 1.88/0.61  fof(f596,plain,(
% 1.88/0.61    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_54),
% 1.88/0.61    inference(avatar_component_clause,[],[f594])).
% 1.88/0.61  fof(f1187,plain,(
% 1.88/0.61    ( ! [X14,X12,X13] : (r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12) | ~r1_tarski(X14,X12) | ~r1_tarski(X13,X12)) ) | ~spl6_97),
% 1.88/0.61    inference(avatar_component_clause,[],[f1186])).
% 1.88/0.61  fof(f1897,plain,(
% 1.88/0.61    spl6_144 | ~spl6_3 | ~spl6_100),
% 1.88/0.61    inference(avatar_split_clause,[],[f1557,f1232,f61,f1895])).
% 1.88/0.61  fof(f61,plain,(
% 1.88/0.61    spl6_3 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.88/0.61  fof(f1232,plain,(
% 1.88/0.61    spl6_100 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 1.88/0.61  fof(f1557,plain,(
% 1.88/0.61    ( ! [X43,X44,X42] : (r1_tarski(k2_zfmisc_1(X42,X43),k2_zfmisc_1(X42,k3_tarski(k1_enumset1(X43,X43,X44))))) ) | (~spl6_3 | ~spl6_100)),
% 1.88/0.61    inference(superposition,[],[f62,f1233])).
% 1.88/0.61  fof(f1233,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ) | ~spl6_100),
% 1.88/0.61    inference(avatar_component_clause,[],[f1232])).
% 1.88/0.61  fof(f62,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) ) | ~spl6_3),
% 1.88/0.61    inference(avatar_component_clause,[],[f61])).
% 1.88/0.61  fof(f1803,plain,(
% 1.88/0.61    spl6_138 | ~spl6_27 | ~spl6_110),
% 1.88/0.61    inference(avatar_split_clause,[],[f1718,f1394,f269,f1801])).
% 1.88/0.61  fof(f269,plain,(
% 1.88/0.61    spl6_27 <=> ! [X1,X0] : (~r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1) | r1_tarski(sK0,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.88/0.61  fof(f1718,plain,(
% 1.88/0.61    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X6)),sK3),X7) | r1_tarski(sK0,X7)) ) | (~spl6_27 | ~spl6_110)),
% 1.88/0.61    inference(superposition,[],[f270,f1395])).
% 1.88/0.61  fof(f270,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1) | r1_tarski(sK0,X1)) ) | ~spl6_27),
% 1.88/0.61    inference(avatar_component_clause,[],[f269])).
% 1.88/0.61  fof(f1684,plain,(
% 1.88/0.61    spl6_133 | ~spl6_24 | ~spl6_100),
% 1.88/0.61    inference(avatar_split_clause,[],[f1553,f1232,f215,f1682])).
% 1.88/0.61  fof(f215,plain,(
% 1.88/0.61    spl6_24 <=> ! [X3,X2] : r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5))))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.88/0.61  fof(f1553,plain,(
% 1.88/0.61    ( ! [X35,X36] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X36,X36,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(X35,X35,sK5))))))) ) | (~spl6_24 | ~spl6_100)),
% 1.88/0.61    inference(superposition,[],[f216,f1233])).
% 1.88/0.61  fof(f216,plain,(
% 1.88/0.61    ( ! [X2,X3] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5))))))) ) | ~spl6_24),
% 1.88/0.61    inference(avatar_component_clause,[],[f215])).
% 1.88/0.61  fof(f1396,plain,(
% 1.88/0.61    spl6_110),
% 1.88/0.61    inference(avatar_split_clause,[],[f46,f1394])).
% 1.88/0.61  fof(f46,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f34,f40,f40])).
% 1.88/0.61  fof(f40,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f31,f30])).
% 1.88/0.61  fof(f30,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f9])).
% 1.88/0.61  fof(f9,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.88/0.61  fof(f31,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f10])).
% 1.88/0.61  fof(f10,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.88/0.61  fof(f34,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.88/0.61  fof(f1234,plain,(
% 1.88/0.61    spl6_100),
% 1.88/0.61    inference(avatar_split_clause,[],[f45,f1232])).
% 1.88/0.61  fof(f45,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f35,f40,f40])).
% 1.88/0.61  fof(f35,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f11])).
% 1.88/0.61  fof(f1188,plain,(
% 1.88/0.61    spl6_97 | ~spl6_64 | ~spl6_80),
% 1.88/0.61    inference(avatar_split_clause,[],[f1073,f879,f723,f1186])).
% 1.88/0.61  fof(f723,plain,(
% 1.88/0.61    spl6_64 <=> ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 1.88/0.61  fof(f879,plain,(
% 1.88/0.61    spl6_80 <=> ! [X1,X3,X0,X2] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 1.88/0.61  fof(f1073,plain,(
% 1.88/0.61    ( ! [X14,X12,X13] : (r1_tarski(k3_tarski(k1_enumset1(X13,X13,X14)),X12) | ~r1_tarski(X14,X12) | ~r1_tarski(X13,X12)) ) | (~spl6_64 | ~spl6_80)),
% 1.88/0.61    inference(superposition,[],[f880,f724])).
% 1.88/0.61  fof(f724,plain,(
% 1.88/0.61    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) ) | ~spl6_64),
% 1.88/0.61    inference(avatar_component_clause,[],[f723])).
% 1.88/0.61  fof(f880,plain,(
% 1.88/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl6_80),
% 1.88/0.61    inference(avatar_component_clause,[],[f879])).
% 1.88/0.61  fof(f881,plain,(
% 1.88/0.61    spl6_80),
% 1.88/0.61    inference(avatar_split_clause,[],[f49,f879])).
% 1.88/0.61  fof(f49,plain,(
% 1.88/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f39,f40,f40])).
% 1.88/0.61  fof(f39,plain,(
% 1.88/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.88/0.61    inference(flattening,[],[f21])).
% 1.88/0.61  fof(f21,plain,(
% 1.88/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.88/0.61  fof(f725,plain,(
% 1.88/0.61    spl6_64 | ~spl6_13 | ~spl6_63),
% 1.88/0.61    inference(avatar_split_clause,[],[f700,f697,f119,f723])).
% 1.88/0.61  fof(f119,plain,(
% 1.88/0.61    spl6_13 <=> ! [X1,X0] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.88/0.61  fof(f697,plain,(
% 1.88/0.61    spl6_63 <=> ! [X0] : r1_tarski(X0,X0)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 1.88/0.61  fof(f700,plain,(
% 1.88/0.61    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) ) | (~spl6_13 | ~spl6_63)),
% 1.88/0.61    inference(resolution,[],[f698,f120])).
% 1.88/0.61  fof(f120,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) ) | ~spl6_13),
% 1.88/0.61    inference(avatar_component_clause,[],[f119])).
% 1.88/0.61  fof(f698,plain,(
% 1.88/0.61    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl6_63),
% 1.88/0.61    inference(avatar_component_clause,[],[f697])).
% 1.88/0.61  fof(f699,plain,(
% 1.88/0.61    spl6_63 | ~spl6_3 | ~spl6_62),
% 1.88/0.61    inference(avatar_split_clause,[],[f680,f667,f61,f697])).
% 1.88/0.61  fof(f667,plain,(
% 1.88/0.61    spl6_62 <=> ! [X1,X0] : k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.88/0.61  fof(f680,plain,(
% 1.88/0.61    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl6_3 | ~spl6_62)),
% 1.88/0.61    inference(superposition,[],[f62,f668])).
% 1.88/0.61  fof(f668,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) ) | ~spl6_62),
% 1.88/0.61    inference(avatar_component_clause,[],[f667])).
% 1.88/0.61  fof(f669,plain,(
% 1.88/0.61    spl6_62 | ~spl6_5 | ~spl6_13 | ~spl6_37),
% 1.88/0.61    inference(avatar_split_clause,[],[f406,f400,f119,f69,f667])).
% 1.88/0.61  fof(f69,plain,(
% 1.88/0.61    spl6_5 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.88/0.61  fof(f400,plain,(
% 1.88/0.61    spl6_37 <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.88/0.61  fof(f406,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) ) | (~spl6_5 | ~spl6_13 | ~spl6_37)),
% 1.88/0.61    inference(forward_demodulation,[],[f403,f70])).
% 1.88/0.61  fof(f70,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) ) | ~spl6_5),
% 1.88/0.61    inference(avatar_component_clause,[],[f69])).
% 1.88/0.61  fof(f403,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0) ) | (~spl6_13 | ~spl6_37)),
% 1.88/0.61    inference(resolution,[],[f401,f120])).
% 1.88/0.61  fof(f401,plain,(
% 1.88/0.61    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)) ) | ~spl6_37),
% 1.88/0.61    inference(avatar_component_clause,[],[f400])).
% 1.88/0.61  fof(f597,plain,(
% 1.88/0.61    ~spl6_54),
% 1.88/0.61    inference(avatar_split_clause,[],[f41,f594])).
% 1.88/0.61  fof(f41,plain,(
% 1.88/0.61    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 1.88/0.61    inference(definition_unfolding,[],[f27,f40,f40,f40])).
% 1.88/0.61  fof(f27,plain,(
% 1.88/0.61    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.88/0.61    inference(cnf_transformation,[],[f24])).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f15,plain,(
% 1.88/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.88/0.61    inference(flattening,[],[f14])).
% 1.88/0.61  fof(f14,plain,(
% 1.88/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.88/0.61    inference(ennf_transformation,[],[f13])).
% 1.88/0.61  fof(f13,negated_conjecture,(
% 1.88/0.61    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.88/0.61    inference(negated_conjecture,[],[f12])).
% 1.88/0.61  fof(f12,conjecture,(
% 1.88/0.61    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.88/0.61  fof(f402,plain,(
% 1.88/0.61    spl6_37 | ~spl6_8 | ~spl6_23),
% 1.88/0.61    inference(avatar_split_clause,[],[f375,f211,f88,f400])).
% 1.88/0.61  fof(f88,plain,(
% 1.88/0.61    spl6_8 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.88/0.61  fof(f211,plain,(
% 1.88/0.61    spl6_23 <=> ! [X1,X0,X2] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.88/0.61  fof(f375,plain,(
% 1.88/0.61    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)) ) | (~spl6_8 | ~spl6_23)),
% 1.88/0.61    inference(resolution,[],[f212,f89])).
% 1.88/0.61  fof(f89,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) ) | ~spl6_8),
% 1.88/0.61    inference(avatar_component_clause,[],[f88])).
% 1.88/0.61  fof(f212,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ) | ~spl6_23),
% 1.88/0.61    inference(avatar_component_clause,[],[f211])).
% 1.88/0.61  fof(f271,plain,(
% 1.88/0.61    spl6_27 | ~spl6_4 | ~spl6_11),
% 1.88/0.61    inference(avatar_split_clause,[],[f122,f111,f65,f269])).
% 1.88/0.61  fof(f65,plain,(
% 1.88/0.61    spl6_4 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.88/0.61  fof(f111,plain,(
% 1.88/0.61    spl6_11 <=> ! [X0] : r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.88/0.61  fof(f122,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)),X1) | r1_tarski(sK0,X1)) ) | (~spl6_4 | ~spl6_11)),
% 1.88/0.61    inference(resolution,[],[f112,f66])).
% 1.88/0.61  fof(f66,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl6_4),
% 1.88/0.61    inference(avatar_component_clause,[],[f65])).
% 1.88/0.61  fof(f112,plain,(
% 1.88/0.61    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)))) ) | ~spl6_11),
% 1.88/0.61    inference(avatar_component_clause,[],[f111])).
% 1.88/0.61  fof(f217,plain,(
% 1.88/0.61    spl6_24 | ~spl6_8 | ~spl6_21),
% 1.88/0.61    inference(avatar_split_clause,[],[f202,f193,f88,f215])).
% 1.88/0.61  fof(f193,plain,(
% 1.88/0.61    spl6_21 <=> ! [X1,X0] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1) | r1_tarski(sK1,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.88/0.61  fof(f202,plain,(
% 1.88/0.61    ( ! [X2,X3] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X3,X3,k2_zfmisc_1(sK4,sK5))))))) ) | (~spl6_8 | ~spl6_21)),
% 1.88/0.61    inference(resolution,[],[f194,f89])).
% 1.88/0.61  fof(f194,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1) | r1_tarski(sK1,X1)) ) | ~spl6_21),
% 1.88/0.61    inference(avatar_component_clause,[],[f193])).
% 1.88/0.61  fof(f213,plain,(
% 1.88/0.61    spl6_23),
% 1.88/0.61    inference(avatar_split_clause,[],[f47,f211])).
% 1.88/0.61  fof(f47,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f36,f32,f40])).
% 1.88/0.61  fof(f32,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f1])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.88/0.61  fof(f36,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f17])).
% 1.88/0.61  fof(f17,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.88/0.61    inference(ennf_transformation,[],[f5])).
% 1.88/0.61  fof(f5,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.88/0.61  fof(f195,plain,(
% 1.88/0.61    spl6_21 | ~spl6_4 | ~spl6_10),
% 1.88/0.61    inference(avatar_split_clause,[],[f107,f101,f65,f193])).
% 1.88/0.61  fof(f101,plain,(
% 1.88/0.61    spl6_10 <=> ! [X4] : r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.88/0.61  fof(f107,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,k2_zfmisc_1(sK4,sK5))),X1) | r1_tarski(sK1,X1)) ) | (~spl6_4 | ~spl6_10)),
% 1.88/0.61    inference(resolution,[],[f102,f66])).
% 1.88/0.61  fof(f102,plain,(
% 1.88/0.61    ( ! [X4] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5))))) ) | ~spl6_10),
% 1.88/0.61    inference(avatar_component_clause,[],[f101])).
% 1.88/0.61  fof(f121,plain,(
% 1.88/0.61    spl6_13),
% 1.88/0.61    inference(avatar_split_clause,[],[f44,f119])).
% 1.88/0.61  fof(f44,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f33,f40])).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f16])).
% 1.88/0.61  fof(f16,plain,(
% 1.88/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.88/0.61    inference(ennf_transformation,[],[f2])).
% 1.88/0.61  fof(f2,axiom,(
% 1.88/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.88/0.61  fof(f113,plain,(
% 1.88/0.61    spl6_11 | ~spl6_3 | ~spl6_6),
% 1.88/0.61    inference(avatar_split_clause,[],[f83,f76,f61,f111])).
% 1.88/0.61  fof(f76,plain,(
% 1.88/0.61    spl6_6 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.88/0.61  fof(f83,plain,(
% 1.88/0.61    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X0)))) ) | (~spl6_3 | ~spl6_6)),
% 1.88/0.61    inference(resolution,[],[f77,f62])).
% 1.88/0.61  fof(f77,plain,(
% 1.88/0.61    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | ~spl6_6),
% 1.88/0.61    inference(avatar_component_clause,[],[f76])).
% 1.88/0.61  fof(f103,plain,(
% 1.88/0.61    spl6_10 | ~spl6_7 | ~spl6_8),
% 1.88/0.61    inference(avatar_split_clause,[],[f93,f88,f80,f101])).
% 1.88/0.61  fof(f80,plain,(
% 1.88/0.61    spl6_7 <=> ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.88/0.61  fof(f93,plain,(
% 1.88/0.61    ( ! [X4] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X4,X4,k2_zfmisc_1(sK4,sK5))))) ) | (~spl6_7 | ~spl6_8)),
% 1.88/0.61    inference(resolution,[],[f89,f81])).
% 1.88/0.61  fof(f81,plain,(
% 1.88/0.61    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) ) | ~spl6_7),
% 1.88/0.61    inference(avatar_component_clause,[],[f80])).
% 1.88/0.61  fof(f90,plain,(
% 1.88/0.61    spl6_8 | ~spl6_3 | ~spl6_5),
% 1.88/0.61    inference(avatar_split_clause,[],[f85,f69,f61,f88])).
% 1.88/0.61  fof(f85,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) ) | (~spl6_3 | ~spl6_5)),
% 1.88/0.61    inference(superposition,[],[f62,f70])).
% 1.88/0.61  fof(f82,plain,(
% 1.88/0.61    spl6_7 | ~spl6_2 | ~spl6_4),
% 1.88/0.61    inference(avatar_split_clause,[],[f73,f65,f56,f80])).
% 1.88/0.61  fof(f56,plain,(
% 1.88/0.61    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.88/0.61  fof(f73,plain,(
% 1.88/0.61    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) ) | (~spl6_2 | ~spl6_4)),
% 1.88/0.61    inference(resolution,[],[f66,f58])).
% 1.88/0.61  fof(f58,plain,(
% 1.88/0.61    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 1.88/0.61    inference(avatar_component_clause,[],[f56])).
% 1.88/0.61  fof(f78,plain,(
% 1.88/0.61    spl6_6 | ~spl6_1 | ~spl6_4),
% 1.88/0.61    inference(avatar_split_clause,[],[f72,f65,f51,f76])).
% 1.88/0.61  fof(f51,plain,(
% 1.88/0.61    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.88/0.61  fof(f72,plain,(
% 1.88/0.61    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | (~spl6_1 | ~spl6_4)),
% 1.88/0.61    inference(resolution,[],[f66,f53])).
% 1.88/0.61  fof(f53,plain,(
% 1.88/0.61    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 1.88/0.61    inference(avatar_component_clause,[],[f51])).
% 1.88/0.61  fof(f71,plain,(
% 1.88/0.61    spl6_5),
% 1.88/0.61    inference(avatar_split_clause,[],[f43,f69])).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f29,f30,f30])).
% 1.88/0.61  fof(f29,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f8])).
% 1.88/0.61  fof(f8,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.88/0.61  fof(f67,plain,(
% 1.88/0.61    spl6_4),
% 1.88/0.61    inference(avatar_split_clause,[],[f38,f65])).
% 1.88/0.61  fof(f38,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f20])).
% 1.88/0.61  fof(f20,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.88/0.61    inference(flattening,[],[f19])).
% 1.88/0.61  fof(f19,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.88/0.61  fof(f63,plain,(
% 1.88/0.61    spl6_3),
% 1.88/0.61    inference(avatar_split_clause,[],[f42,f61])).
% 1.88/0.61  fof(f42,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f28,f40])).
% 1.88/0.61  fof(f28,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,axiom,(
% 1.88/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.88/0.61  fof(f59,plain,(
% 1.88/0.61    spl6_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f26,f56])).
% 1.88/0.61  fof(f26,plain,(
% 1.88/0.61    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.88/0.61    inference(cnf_transformation,[],[f24])).
% 1.88/0.61  fof(f54,plain,(
% 1.88/0.61    spl6_1),
% 1.88/0.61    inference(avatar_split_clause,[],[f25,f51])).
% 1.88/0.61  fof(f25,plain,(
% 1.88/0.61    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.88/0.61    inference(cnf_transformation,[],[f24])).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (1679)------------------------------
% 1.88/0.61  % (1679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (1679)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (1679)Memory used [KB]: 8571
% 1.88/0.61  % (1679)Time elapsed: 0.203 s
% 1.88/0.61  % (1679)------------------------------
% 1.88/0.61  % (1679)------------------------------
% 1.88/0.61  % (1668)Success in time 0.26 s
%------------------------------------------------------------------------------
