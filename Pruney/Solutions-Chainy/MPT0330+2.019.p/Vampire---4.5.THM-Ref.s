%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:01 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 317 expanded)
%              Number of leaves         :   33 ( 137 expanded)
%              Depth                    :    8
%              Number of atoms          :  298 ( 625 expanded)
%              Number of equality atoms :   26 ( 153 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2461,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f59,f63,f69,f73,f106,f110,f114,f122,f134,f167,f185,f277,f366,f478,f729,f1156,f1186,f1204,f1498,f2400,f2457])).

fof(f2457,plain,
    ( ~ spl6_85
    | spl6_108
    | ~ spl6_148 ),
    inference(avatar_contradiction_clause,[],[f2456])).

fof(f2456,plain,
    ( $false
    | ~ spl6_85
    | spl6_108
    | ~ spl6_148 ),
    inference(subsumption_resolution,[],[f1497,f2428])).

fof(f2428,plain,
    ( ! [X30,X31] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X30,X30,X30,X30,sK4)),k3_tarski(k3_enumset1(X31,X31,X31,X31,sK5))))
    | ~ spl6_85
    | ~ spl6_148 ),
    inference(resolution,[],[f2399,f1185])).

fof(f1185,plain,
    ( ! [X30,X29] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30)
        | r1_tarski(sK1,X30) )
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f1184,plain,
    ( spl6_85
  <=> ! [X29,X30] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30)
        | r1_tarski(sK1,X30) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f2399,plain,
    ( ! [X59,X57,X58] : r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59))))
    | ~ spl6_148 ),
    inference(avatar_component_clause,[],[f2398])).

fof(f2398,plain,
    ( spl6_148
  <=> ! [X58,X57,X59] : r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f1497,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_108 ),
    inference(avatar_component_clause,[],[f1495])).

fof(f1495,plain,
    ( spl6_108
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f2400,plain,
    ( spl6_148
    | ~ spl6_15
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f903,f476,f132,f2398])).

fof(f132,plain,
    ( spl6_15
  <=> ! [X3,X4] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f476,plain,
    ( spl6_44
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f903,plain,
    ( ! [X59,X57,X58] : r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59))))
    | ~ spl6_15
    | ~ spl6_44 ),
    inference(superposition,[],[f133,f477])).

fof(f477,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f476])).

fof(f133,plain,
    ( ! [X4,X3] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1498,plain,
    ( ~ spl6_108
    | ~ spl6_14
    | spl6_33
    | ~ spl6_82
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f1244,f1202,f1154,f363,f120,f1495])).

fof(f120,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f363,plain,
    ( spl6_33
  <=> r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1154,plain,
    ( spl6_82
  <=> ! [X5,X4] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5)
        | r1_tarski(sK0,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f1202,plain,
    ( spl6_86
  <=> ! [X40,X42,X41] : r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f1244,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ spl6_14
    | spl6_33
    | ~ spl6_82
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f430,f1217])).

fof(f1217,plain,
    ( ! [X12,X13] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X12)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X13))))
    | ~ spl6_82
    | ~ spl6_86 ),
    inference(resolution,[],[f1203,f1155])).

fof(f1155,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5)
        | r1_tarski(sK0,X5) )
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1203,plain,
    ( ! [X41,X42,X40] : r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42))))
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f430,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ spl6_14
    | spl6_33 ),
    inference(resolution,[],[f365,f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f365,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f363])).

fof(f1204,plain,
    ( spl6_86
    | ~ spl6_4
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f898,f476,f61,f1202])).

fof(f61,plain,
    ( spl6_4
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f898,plain,
    ( ! [X41,X42,X40] : r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42))))
    | ~ spl6_4
    | ~ spl6_44 ),
    inference(superposition,[],[f62,f477])).

fof(f62,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f1186,plain,
    ( spl6_85
    | ~ spl6_21
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f1058,f727,f183,f1184])).

fof(f183,plain,
    ( spl6_21
  <=> ! [X1,X2] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2)
        | r1_tarski(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f727,plain,
    ( spl6_55
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f1058,plain,
    ( ! [X30,X29] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30)
        | r1_tarski(sK1,X30) )
    | ~ spl6_21
    | ~ spl6_55 ),
    inference(superposition,[],[f184,f728])).

fof(f728,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f727])).

fof(f184,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2)
        | r1_tarski(sK1,X2) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f183])).

fof(f1156,plain,
    ( spl6_82
    | ~ spl6_27
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f1043,f727,f275,f1154])).

fof(f275,plain,
    ( spl6_27
  <=> ! [X1,X2] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2)
        | r1_tarski(sK0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1043,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5)
        | r1_tarski(sK0,X5) )
    | ~ spl6_27
    | ~ spl6_55 ),
    inference(superposition,[],[f276,f728])).

fof(f276,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2)
        | r1_tarski(sK0,X2) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f275])).

fof(f729,plain,(
    spl6_55 ),
    inference(avatar_split_clause,[],[f44,f727])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f31,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f478,plain,(
    spl6_44 ),
    inference(avatar_split_clause,[],[f43,f476])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f32,f38,f38])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f366,plain,(
    ~ spl6_33 ),
    inference(avatar_split_clause,[],[f39,f363])).

fof(f39,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f24,f38,f38,f38])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f277,plain,
    ( spl6_27
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f116,f104,f57,f275])).

fof(f57,plain,
    ( spl6_3
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f104,plain,
    ( spl6_11
  <=> ! [X3] : r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f116,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2)
        | r1_tarski(sK0,X2) )
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f105,plain,
    ( ! [X3] : r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f185,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f174,f165,f57,f183])).

fof(f165,plain,
    ( spl6_19
  <=> ! [X6] : r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f174,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2)
        | r1_tarski(sK1,X2) )
    | ~ spl6_3
    | ~ spl6_19 ),
    inference(resolution,[],[f166,f58])).

fof(f166,plain,
    ( ! [X6] : r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl6_19
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f126,f112,f108,f165])).

fof(f108,plain,
    ( spl6_12
  <=> ! [X4] : r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f112,plain,
    ( spl6_13
  <=> ! [X1,X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f126,plain,
    ( ! [X6] : r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(superposition,[],[f109,f113])).

fof(f113,plain,
    ( ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f109,plain,
    ( ! [X4] : r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f134,plain,
    ( spl6_15
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f124,f112,f61,f132])).

fof(f124,plain,
    ( ! [X4,X3] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(superposition,[],[f62,f113])).

fof(f122,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f114,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f41,f112])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f38,f38])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f110,plain,
    ( spl6_12
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f76,f71,f61,f108])).

fof(f71,plain,
    ( spl6_6
  <=> ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f76,plain,
    ( ! [X4] : r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4)))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f106,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f75,f67,f61,f104])).

fof(f67,plain,
    ( spl6_5
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f75,plain,
    ( ! [X3] : r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,
    ( spl6_6
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f65,f57,f52,f71])).

fof(f52,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f65,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f69,plain,
    ( spl6_5
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f64,f57,f47,f67])).

fof(f47,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f63,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f59,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (9139)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (9132)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (9129)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (9141)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (9133)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (9140)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (9144)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (9128)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (9143)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (9136)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (9127)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (9130)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (9138)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (9131)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (9142)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (9135)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (9137)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (9134)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 3.29/0.83  % (9134)Refutation found. Thanks to Tanya!
% 3.29/0.83  % SZS status Theorem for theBenchmark
% 3.29/0.83  % SZS output start Proof for theBenchmark
% 3.29/0.83  fof(f2461,plain,(
% 3.29/0.83    $false),
% 3.29/0.83    inference(avatar_sat_refutation,[],[f50,f55,f59,f63,f69,f73,f106,f110,f114,f122,f134,f167,f185,f277,f366,f478,f729,f1156,f1186,f1204,f1498,f2400,f2457])).
% 3.29/0.83  fof(f2457,plain,(
% 3.29/0.83    ~spl6_85 | spl6_108 | ~spl6_148),
% 3.29/0.83    inference(avatar_contradiction_clause,[],[f2456])).
% 3.29/0.83  fof(f2456,plain,(
% 3.29/0.83    $false | (~spl6_85 | spl6_108 | ~spl6_148)),
% 3.29/0.83    inference(subsumption_resolution,[],[f1497,f2428])).
% 3.29/0.83  fof(f2428,plain,(
% 3.29/0.83    ( ! [X30,X31] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X30,X30,X30,X30,sK4)),k3_tarski(k3_enumset1(X31,X31,X31,X31,sK5))))) ) | (~spl6_85 | ~spl6_148)),
% 3.29/0.83    inference(resolution,[],[f2399,f1185])).
% 3.29/0.83  fof(f1185,plain,(
% 3.29/0.83    ( ! [X30,X29] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30) | r1_tarski(sK1,X30)) ) | ~spl6_85),
% 3.29/0.83    inference(avatar_component_clause,[],[f1184])).
% 3.29/0.83  fof(f1184,plain,(
% 3.29/0.83    spl6_85 <=> ! [X29,X30] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30) | r1_tarski(sK1,X30))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 3.29/0.83  fof(f2399,plain,(
% 3.29/0.83    ( ! [X59,X57,X58] : (r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59))))) ) | ~spl6_148),
% 3.29/0.83    inference(avatar_component_clause,[],[f2398])).
% 3.29/0.83  fof(f2398,plain,(
% 3.29/0.83    spl6_148 <=> ! [X58,X57,X59] : r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59))))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).
% 3.29/0.83  fof(f1497,plain,(
% 3.29/0.83    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_108),
% 3.29/0.83    inference(avatar_component_clause,[],[f1495])).
% 3.29/0.83  fof(f1495,plain,(
% 3.29/0.83    spl6_108 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).
% 3.29/0.83  fof(f2400,plain,(
% 3.29/0.83    spl6_148 | ~spl6_15 | ~spl6_44),
% 3.29/0.83    inference(avatar_split_clause,[],[f903,f476,f132,f2398])).
% 3.29/0.83  fof(f132,plain,(
% 3.29/0.83    spl6_15 <=> ! [X3,X4] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.29/0.83  fof(f476,plain,(
% 3.29/0.83    spl6_44 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 3.29/0.83  fof(f903,plain,(
% 3.29/0.83    ( ! [X59,X57,X58] : (r1_tarski(k2_zfmisc_1(X57,X59),k2_zfmisc_1(X57,k3_tarski(k3_enumset1(X58,X58,X58,X58,X59))))) ) | (~spl6_15 | ~spl6_44)),
% 3.29/0.83    inference(superposition,[],[f133,f477])).
% 3.29/0.83  fof(f477,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ) | ~spl6_44),
% 3.29/0.83    inference(avatar_component_clause,[],[f476])).
% 3.29/0.83  fof(f133,plain,(
% 3.29/0.83    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))) ) | ~spl6_15),
% 3.29/0.83    inference(avatar_component_clause,[],[f132])).
% 3.29/0.83  fof(f1498,plain,(
% 3.29/0.83    ~spl6_108 | ~spl6_14 | spl6_33 | ~spl6_82 | ~spl6_86),
% 3.29/0.83    inference(avatar_split_clause,[],[f1244,f1202,f1154,f363,f120,f1495])).
% 3.29/0.83  fof(f120,plain,(
% 3.29/0.83    spl6_14 <=> ! [X1,X0,X2] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 3.29/0.83  fof(f363,plain,(
% 3.29/0.83    spl6_33 <=> r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 3.29/0.83  fof(f1154,plain,(
% 3.29/0.83    spl6_82 <=> ! [X5,X4] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5) | r1_tarski(sK0,X5))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 3.29/0.83  fof(f1202,plain,(
% 3.29/0.83    spl6_86 <=> ! [X40,X42,X41] : r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42))))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 3.29/0.83  fof(f1244,plain,(
% 3.29/0.83    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | (~spl6_14 | spl6_33 | ~spl6_82 | ~spl6_86)),
% 3.29/0.83    inference(subsumption_resolution,[],[f430,f1217])).
% 3.29/0.83  fof(f1217,plain,(
% 3.29/0.83    ( ! [X12,X13] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X12)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X13))))) ) | (~spl6_82 | ~spl6_86)),
% 3.29/0.83    inference(resolution,[],[f1203,f1155])).
% 3.29/0.83  fof(f1155,plain,(
% 3.29/0.83    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5) | r1_tarski(sK0,X5)) ) | ~spl6_82),
% 3.29/0.83    inference(avatar_component_clause,[],[f1154])).
% 3.29/0.83  fof(f1203,plain,(
% 3.29/0.83    ( ! [X41,X42,X40] : (r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42))))) ) | ~spl6_86),
% 3.29/0.83    inference(avatar_component_clause,[],[f1202])).
% 3.29/0.83  fof(f430,plain,(
% 3.29/0.83    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | (~spl6_14 | spl6_33)),
% 3.29/0.83    inference(resolution,[],[f365,f121])).
% 3.29/0.83  fof(f121,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl6_14),
% 3.29/0.83    inference(avatar_component_clause,[],[f120])).
% 3.29/0.83  fof(f365,plain,(
% 3.29/0.83    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | spl6_33),
% 3.29/0.83    inference(avatar_component_clause,[],[f363])).
% 3.29/0.83  fof(f1204,plain,(
% 3.29/0.83    spl6_86 | ~spl6_4 | ~spl6_44),
% 3.29/0.83    inference(avatar_split_clause,[],[f898,f476,f61,f1202])).
% 3.29/0.83  fof(f61,plain,(
% 3.29/0.83    spl6_4 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.29/0.83  fof(f898,plain,(
% 3.29/0.83    ( ! [X41,X42,X40] : (r1_tarski(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k3_tarski(k3_enumset1(X41,X41,X41,X41,X42))))) ) | (~spl6_4 | ~spl6_44)),
% 3.29/0.83    inference(superposition,[],[f62,f477])).
% 3.29/0.83  fof(f62,plain,(
% 3.29/0.83    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ) | ~spl6_4),
% 3.29/0.83    inference(avatar_component_clause,[],[f61])).
% 3.29/0.83  fof(f1186,plain,(
% 3.29/0.83    spl6_85 | ~spl6_21 | ~spl6_55),
% 3.29/0.83    inference(avatar_split_clause,[],[f1058,f727,f183,f1184])).
% 3.29/0.83  fof(f183,plain,(
% 3.29/0.83    spl6_21 <=> ! [X1,X2] : (~r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2) | r1_tarski(sK1,X2))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 3.29/0.83  fof(f727,plain,(
% 3.29/0.83    spl6_55 <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 3.29/0.83  fof(f1058,plain,(
% 3.29/0.83    ( ! [X30,X29] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X29,X29,X29,X29,sK4)),sK5),X30) | r1_tarski(sK1,X30)) ) | (~spl6_21 | ~spl6_55)),
% 3.29/0.83    inference(superposition,[],[f184,f728])).
% 3.29/0.83  fof(f728,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ) | ~spl6_55),
% 3.29/0.83    inference(avatar_component_clause,[],[f727])).
% 3.29/0.83  fof(f184,plain,(
% 3.29/0.83    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2) | r1_tarski(sK1,X2)) ) | ~spl6_21),
% 3.29/0.83    inference(avatar_component_clause,[],[f183])).
% 3.29/0.83  fof(f1156,plain,(
% 3.29/0.83    spl6_82 | ~spl6_27 | ~spl6_55),
% 3.29/0.83    inference(avatar_split_clause,[],[f1043,f727,f275,f1154])).
% 3.29/0.83  fof(f275,plain,(
% 3.29/0.83    spl6_27 <=> ! [X1,X2] : (~r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2) | r1_tarski(sK0,X2))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 3.29/0.83  fof(f1043,plain,(
% 3.29/0.83    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X4)),sK3),X5) | r1_tarski(sK0,X5)) ) | (~spl6_27 | ~spl6_55)),
% 3.29/0.83    inference(superposition,[],[f276,f728])).
% 3.29/0.83  fof(f276,plain,(
% 3.29/0.83    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2) | r1_tarski(sK0,X2)) ) | ~spl6_27),
% 3.29/0.83    inference(avatar_component_clause,[],[f275])).
% 3.29/0.83  fof(f729,plain,(
% 3.29/0.83    spl6_55),
% 3.29/0.83    inference(avatar_split_clause,[],[f44,f727])).
% 3.29/0.83  fof(f44,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) = k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 3.29/0.83    inference(definition_unfolding,[],[f31,f38,f38])).
% 3.29/0.83  fof(f38,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.29/0.83    inference(definition_unfolding,[],[f27,f37])).
% 3.29/0.83  fof(f37,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.29/0.83    inference(definition_unfolding,[],[f28,f36])).
% 3.29/0.83  fof(f36,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.29/0.83    inference(definition_unfolding,[],[f30,f35])).
% 3.29/0.83  fof(f35,plain,(
% 3.29/0.83    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f8])).
% 3.29/0.83  fof(f8,axiom,(
% 3.29/0.83    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.29/0.83  fof(f30,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f7])).
% 3.29/0.83  fof(f7,axiom,(
% 3.29/0.83    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.29/0.83  fof(f28,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f6])).
% 3.29/0.83  fof(f6,axiom,(
% 3.29/0.83    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.29/0.83  fof(f27,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.29/0.83    inference(cnf_transformation,[],[f9])).
% 3.29/0.83  fof(f9,axiom,(
% 3.29/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.29/0.83  fof(f31,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 3.29/0.83    inference(cnf_transformation,[],[f10])).
% 3.29/0.83  fof(f10,axiom,(
% 3.29/0.83    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 3.29/0.83  fof(f478,plain,(
% 3.29/0.83    spl6_44),
% 3.29/0.83    inference(avatar_split_clause,[],[f43,f476])).
% 3.29/0.83  fof(f43,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 3.29/0.83    inference(definition_unfolding,[],[f32,f38,f38])).
% 3.29/0.83  fof(f32,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 3.29/0.83    inference(cnf_transformation,[],[f10])).
% 3.29/0.83  fof(f366,plain,(
% 3.29/0.83    ~spl6_33),
% 3.29/0.83    inference(avatar_split_clause,[],[f39,f363])).
% 3.29/0.83  fof(f39,plain,(
% 3.29/0.83    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 3.29/0.83    inference(definition_unfolding,[],[f24,f38,f38,f38])).
% 3.29/0.83  fof(f24,plain,(
% 3.29/0.83    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 3.29/0.83    inference(cnf_transformation,[],[f21])).
% 3.29/0.83  fof(f21,plain,(
% 3.29/0.83    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.29/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f20])).
% 3.29/0.83  fof(f20,plain,(
% 3.29/0.83    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 3.29/0.83    introduced(choice_axiom,[])).
% 3.29/0.83  fof(f14,plain,(
% 3.29/0.83    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 3.29/0.83    inference(flattening,[],[f13])).
% 3.29/0.83  fof(f13,plain,(
% 3.29/0.83    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 3.29/0.83    inference(ennf_transformation,[],[f12])).
% 3.29/0.83  fof(f12,negated_conjecture,(
% 3.29/0.83    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.29/0.83    inference(negated_conjecture,[],[f11])).
% 3.29/0.83  fof(f11,conjecture,(
% 3.29/0.83    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 3.29/0.83  fof(f277,plain,(
% 3.29/0.83    spl6_27 | ~spl6_3 | ~spl6_11),
% 3.29/0.83    inference(avatar_split_clause,[],[f116,f104,f57,f275])).
% 3.29/0.83  fof(f57,plain,(
% 3.29/0.83    spl6_3 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.29/0.83  fof(f104,plain,(
% 3.29/0.83    spl6_11 <=> ! [X3] : r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.29/0.83  fof(f116,plain,(
% 3.29/0.83    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X1)),X2) | r1_tarski(sK0,X2)) ) | (~spl6_3 | ~spl6_11)),
% 3.29/0.83    inference(resolution,[],[f105,f58])).
% 3.29/0.83  fof(f58,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl6_3),
% 3.29/0.83    inference(avatar_component_clause,[],[f57])).
% 3.29/0.83  fof(f105,plain,(
% 3.29/0.83    ( ! [X3] : (r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))) ) | ~spl6_11),
% 3.29/0.83    inference(avatar_component_clause,[],[f104])).
% 3.29/0.83  fof(f185,plain,(
% 3.29/0.83    spl6_21 | ~spl6_3 | ~spl6_19),
% 3.29/0.83    inference(avatar_split_clause,[],[f174,f165,f57,f183])).
% 3.29/0.83  fof(f165,plain,(
% 3.29/0.83    spl6_19 <=> ! [X6] : r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5))))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 3.29/0.83  fof(f174,plain,(
% 3.29/0.83    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(sK4,sK5))),X2) | r1_tarski(sK1,X2)) ) | (~spl6_3 | ~spl6_19)),
% 3.29/0.83    inference(resolution,[],[f166,f58])).
% 3.29/0.83  fof(f166,plain,(
% 3.29/0.83    ( ! [X6] : (r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5))))) ) | ~spl6_19),
% 3.29/0.83    inference(avatar_component_clause,[],[f165])).
% 3.29/0.83  fof(f167,plain,(
% 3.29/0.83    spl6_19 | ~spl6_12 | ~spl6_13),
% 3.29/0.83    inference(avatar_split_clause,[],[f126,f112,f108,f165])).
% 3.29/0.83  fof(f108,plain,(
% 3.29/0.83    spl6_12 <=> ! [X4] : r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4)))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 3.29/0.83  fof(f112,plain,(
% 3.29/0.83    spl6_13 <=> ! [X1,X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 3.29/0.83  fof(f126,plain,(
% 3.29/0.83    ( ! [X6] : (r1_tarski(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,k2_zfmisc_1(sK4,sK5))))) ) | (~spl6_12 | ~spl6_13)),
% 3.29/0.83    inference(superposition,[],[f109,f113])).
% 3.29/0.83  fof(f113,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ) | ~spl6_13),
% 3.29/0.83    inference(avatar_component_clause,[],[f112])).
% 3.29/0.83  fof(f109,plain,(
% 3.29/0.83    ( ! [X4] : (r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4)))) ) | ~spl6_12),
% 3.29/0.83    inference(avatar_component_clause,[],[f108])).
% 3.29/0.83  fof(f134,plain,(
% 3.29/0.83    spl6_15 | ~spl6_4 | ~spl6_13),
% 3.29/0.83    inference(avatar_split_clause,[],[f124,f112,f61,f132])).
% 3.29/0.83  fof(f124,plain,(
% 3.29/0.83    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))) ) | (~spl6_4 | ~spl6_13)),
% 3.29/0.83    inference(superposition,[],[f62,f113])).
% 3.29/0.83  fof(f122,plain,(
% 3.29/0.83    spl6_14),
% 3.29/0.83    inference(avatar_split_clause,[],[f45,f120])).
% 3.29/0.83  fof(f45,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.29/0.83    inference(definition_unfolding,[],[f34,f38])).
% 3.29/0.83  fof(f34,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f19])).
% 3.29/0.83  fof(f19,plain,(
% 3.29/0.83    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.29/0.83    inference(flattening,[],[f18])).
% 3.29/0.83  fof(f18,plain,(
% 3.29/0.83    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.29/0.83    inference(ennf_transformation,[],[f5])).
% 3.29/0.83  fof(f5,axiom,(
% 3.29/0.83    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.29/0.83  fof(f114,plain,(
% 3.29/0.83    spl6_13),
% 3.29/0.83    inference(avatar_split_clause,[],[f41,f112])).
% 3.29/0.83  fof(f41,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 3.29/0.83    inference(definition_unfolding,[],[f26,f38,f38])).
% 3.29/0.83  fof(f26,plain,(
% 3.29/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f1])).
% 3.29/0.83  fof(f1,axiom,(
% 3.29/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.29/0.83  fof(f110,plain,(
% 3.29/0.83    spl6_12 | ~spl6_4 | ~spl6_6),
% 3.29/0.83    inference(avatar_split_clause,[],[f76,f71,f61,f108])).
% 3.29/0.83  fof(f71,plain,(
% 3.29/0.83    spl6_6 <=> ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.29/0.83  fof(f76,plain,(
% 3.29/0.83    ( ! [X4] : (r1_tarski(sK1,k3_tarski(k3_enumset1(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5),X4)))) ) | (~spl6_4 | ~spl6_6)),
% 3.29/0.83    inference(resolution,[],[f62,f72])).
% 3.29/0.83  fof(f72,plain,(
% 3.29/0.83    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) ) | ~spl6_6),
% 3.29/0.83    inference(avatar_component_clause,[],[f71])).
% 3.29/0.83  fof(f106,plain,(
% 3.29/0.83    spl6_11 | ~spl6_4 | ~spl6_5),
% 3.29/0.83    inference(avatar_split_clause,[],[f75,f67,f61,f104])).
% 3.29/0.83  fof(f67,plain,(
% 3.29/0.83    spl6_5 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.29/0.83  fof(f75,plain,(
% 3.29/0.83    ( ! [X3] : (r1_tarski(sK0,k3_tarski(k3_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))) ) | (~spl6_4 | ~spl6_5)),
% 3.29/0.83    inference(resolution,[],[f62,f68])).
% 3.29/0.83  fof(f68,plain,(
% 3.29/0.83    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | ~spl6_5),
% 3.29/0.83    inference(avatar_component_clause,[],[f67])).
% 3.29/0.83  fof(f73,plain,(
% 3.29/0.83    spl6_6 | ~spl6_2 | ~spl6_3),
% 3.29/0.83    inference(avatar_split_clause,[],[f65,f57,f52,f71])).
% 3.29/0.83  fof(f52,plain,(
% 3.29/0.83    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.29/0.83  fof(f65,plain,(
% 3.29/0.83    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) ) | (~spl6_2 | ~spl6_3)),
% 3.29/0.83    inference(resolution,[],[f58,f54])).
% 3.29/0.83  fof(f54,plain,(
% 3.29/0.83    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 3.29/0.83    inference(avatar_component_clause,[],[f52])).
% 3.29/0.83  fof(f69,plain,(
% 3.29/0.83    spl6_5 | ~spl6_1 | ~spl6_3),
% 3.29/0.83    inference(avatar_split_clause,[],[f64,f57,f47,f67])).
% 3.29/0.83  fof(f47,plain,(
% 3.29/0.83    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.29/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.29/0.83  fof(f64,plain,(
% 3.29/0.83    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | (~spl6_1 | ~spl6_3)),
% 3.29/0.83    inference(resolution,[],[f58,f49])).
% 3.29/0.83  fof(f49,plain,(
% 3.29/0.83    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 3.29/0.83    inference(avatar_component_clause,[],[f47])).
% 3.29/0.83  fof(f63,plain,(
% 3.29/0.83    spl6_4),
% 3.29/0.83    inference(avatar_split_clause,[],[f40,f61])).
% 3.29/0.83  fof(f40,plain,(
% 3.29/0.83    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.29/0.83    inference(definition_unfolding,[],[f25,f38])).
% 3.29/0.83  fof(f25,plain,(
% 3.29/0.83    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.29/0.83    inference(cnf_transformation,[],[f4])).
% 3.29/0.83  fof(f4,axiom,(
% 3.29/0.83    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.29/0.83  fof(f59,plain,(
% 3.29/0.83    spl6_3),
% 3.29/0.83    inference(avatar_split_clause,[],[f33,f57])).
% 3.29/0.83  fof(f33,plain,(
% 3.29/0.83    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.29/0.83    inference(cnf_transformation,[],[f17])).
% 3.29/0.83  fof(f17,plain,(
% 3.29/0.83    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/0.83    inference(flattening,[],[f16])).
% 3.29/0.83  fof(f16,plain,(
% 3.29/0.83    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.29/0.83    inference(ennf_transformation,[],[f3])).
% 3.29/0.83  fof(f3,axiom,(
% 3.29/0.83    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.29/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.29/0.83  fof(f55,plain,(
% 3.29/0.83    spl6_2),
% 3.29/0.83    inference(avatar_split_clause,[],[f23,f52])).
% 3.29/0.83  fof(f23,plain,(
% 3.29/0.83    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 3.29/0.83    inference(cnf_transformation,[],[f21])).
% 3.29/0.83  fof(f50,plain,(
% 3.29/0.83    spl6_1),
% 3.29/0.83    inference(avatar_split_clause,[],[f22,f47])).
% 3.29/0.83  fof(f22,plain,(
% 3.29/0.83    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.29/0.83    inference(cnf_transformation,[],[f21])).
% 3.29/0.83  % SZS output end Proof for theBenchmark
% 3.29/0.83  % (9134)------------------------------
% 3.29/0.83  % (9134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.83  % (9134)Termination reason: Refutation
% 3.29/0.83  
% 3.29/0.83  % (9134)Memory used [KB]: 10618
% 3.29/0.83  % (9134)Time elapsed: 0.414 s
% 3.29/0.83  % (9134)------------------------------
% 3.29/0.83  % (9134)------------------------------
% 3.29/0.83  % (9126)Success in time 0.469 s
%------------------------------------------------------------------------------
