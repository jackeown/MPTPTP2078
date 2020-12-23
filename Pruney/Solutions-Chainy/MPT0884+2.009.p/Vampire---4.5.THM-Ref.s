%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:56 EST 2020

% Result     : Theorem 6.88s
% Output     : Refutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 238 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :    7
%              Number of atoms          :  145 ( 331 expanded)
%              Number of equality atoms :   71 ( 225 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f152,f156,f188,f612,f832,f856,f2759,f4790,f4936])).

fof(f4936,plain,
    ( ~ spl5_12
    | ~ spl5_35
    | spl5_95
    | ~ spl5_106 ),
    inference(avatar_contradiction_clause,[],[f4935])).

fof(f4935,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_35
    | spl5_95
    | ~ spl5_106 ),
    inference(subsumption_resolution,[],[f4932,f2079])).

fof(f2079,plain,
    ( ! [X152,X151,X149,X150,X148] : k3_enumset1(k4_tarski(k4_tarski(X148,X149),X151),k4_tarski(k4_tarski(X148,X149),X151),k4_tarski(k4_tarski(X148,X149),X152),k4_tarski(k4_tarski(X150,X149),X151),k4_tarski(k4_tarski(X150,X149),X152)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X148,X148,X148,X148,X150),k3_enumset1(X149,X149,X149,X149,X149)),k3_enumset1(X151,X151,X151,X151,X152))
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(superposition,[],[f831,f151])).

fof(f151,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f831,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl5_35
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f4932,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))
    | spl5_95
    | ~ spl5_106 ),
    inference(superposition,[],[f2758,f4789])).

fof(f4789,plain,
    ( ! [X39,X43,X41,X42,X40] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f4788])).

fof(f4788,plain,
    ( spl5_106
  <=> ! [X40,X42,X41,X43,X39] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f2758,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))
    | spl5_95 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f2756,plain,
    ( spl5_95
  <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f4790,plain,
    ( spl5_106
    | ~ spl5_32
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f4765,f854,f610,f4788])).

fof(f610,plain,
    ( spl5_32
  <=> ! [X16,X13,X15,X12,X14] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f854,plain,
    ( spl5_41
  <=> ! [X27,X29,X26,X28,X30] : k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f4765,plain,
    ( ! [X39,X43,X41,X42,X40] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)
    | ~ spl5_32
    | ~ spl5_41 ),
    inference(superposition,[],[f855,f611])).

fof(f611,plain,
    ( ! [X14,X12,X15,X13,X16] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f610])).

fof(f855,plain,
    ( ! [X30,X28,X26,X29,X27] : k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f854])).

fof(f2759,plain,(
    ~ spl5_95 ),
    inference(avatar_split_clause,[],[f37,f2756])).

fof(f37,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    inference(definition_unfolding,[],[f18,f23,f33,f34,f33,f29,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

fof(f856,plain,
    ( spl5_41
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f211,f186,f154,f854])).

fof(f154,plain,
    ( spl5_13
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f186,plain,
    ( spl5_17
  <=> ! [X11,X10,X12] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f211,plain,
    ( ! [X30,X28,X26,X29,X27] : k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(superposition,[],[f155,f187])).

fof(f187,plain,
    ( ! [X12,X10,X11] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f155,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f832,plain,(
    spl5_35 ),
    inference(avatar_split_clause,[],[f42,f830])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f30,f33,f33,f29])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f612,plain,
    ( spl5_32
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f172,f154,f90,f610])).

fof(f90,plain,
    ( spl5_7
  <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f172,plain,
    ( ! [X14,X12,X15,X13,X16] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(superposition,[],[f155,f91])).

fof(f91,plain,
    ( ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f188,plain,
    ( spl5_17
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f174,f154,f70,f186])).

fof(f70,plain,
    ( spl5_6
  <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f174,plain,
    ( ! [X12,X10,X11] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(superposition,[],[f155,f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f156,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f73,f66,f48,f154])).

fof(f48,plain,
    ( spl5_2
  <=> ! [X1,X0] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,
    ( spl5_5
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f73,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f67,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f67,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f152,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f40,f150])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f28,f33,f34,f33])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f92,plain,
    ( spl5_7
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f83,f70,f66,f90])).

fof(f83,plain,
    ( ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f71,f67])).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f26,f32,f33,f34])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f31,f33,f32])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f48])).

fof(f38,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f33,f33])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (827097088)
% 0.21/0.39  ipcrm: permission denied for id (827162650)
% 0.21/0.39  ipcrm: permission denied for id (827195422)
% 0.21/0.48  ipcrm: permission denied for id (827261024)
% 0.21/0.50  ipcrm: permission denied for id (827293812)
% 0.71/0.61  % (21028)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.71/0.62  % (21027)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.71/0.62  % (21033)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.71/0.62  % (21036)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.71/0.63  % (21036)Refutation not found, incomplete strategy% (21036)------------------------------
% 0.71/0.63  % (21036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.71/0.63  % (21036)Termination reason: Refutation not found, incomplete strategy
% 0.71/0.63  
% 0.71/0.63  % (21036)Memory used [KB]: 10618
% 0.71/0.63  % (21036)Time elapsed: 0.075 s
% 0.71/0.63  % (21036)------------------------------
% 0.71/0.63  % (21036)------------------------------
% 0.71/0.63  % (21037)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.71/0.63  % (21031)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.71/0.63  % (21041)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.71/0.63  % (21040)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.71/0.63  % (21032)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.18/0.64  % (21029)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.18/0.64  % (21039)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.18/0.65  % (21035)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.18/0.65  % (21026)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.18/0.65  % (21034)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.18/0.65  % (21038)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.18/0.65  % (21030)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.34/0.66  % (21025)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.34/0.66  % (21042)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.22/1.18  % (21029)Time limit reached!
% 5.22/1.18  % (21029)------------------------------
% 5.22/1.18  % (21029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.53/1.19  % (21029)Termination reason: Time limit
% 5.53/1.19  
% 5.53/1.19  % (21029)Memory used [KB]: 14456
% 5.53/1.19  % (21029)Time elapsed: 0.606 s
% 5.53/1.19  % (21029)------------------------------
% 5.53/1.19  % (21029)------------------------------
% 6.88/1.41  % (21032)Refutation found. Thanks to Tanya!
% 6.88/1.41  % SZS status Theorem for theBenchmark
% 6.88/1.41  % SZS output start Proof for theBenchmark
% 6.88/1.41  fof(f4937,plain,(
% 6.88/1.41    $false),
% 6.88/1.41    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f152,f156,f188,f612,f832,f856,f2759,f4790,f4936])).
% 6.88/1.42  fof(f4936,plain,(
% 6.88/1.42    ~spl5_12 | ~spl5_35 | spl5_95 | ~spl5_106),
% 6.88/1.42    inference(avatar_contradiction_clause,[],[f4935])).
% 6.88/1.42  fof(f4935,plain,(
% 6.88/1.42    $false | (~spl5_12 | ~spl5_35 | spl5_95 | ~spl5_106)),
% 6.88/1.42    inference(subsumption_resolution,[],[f4932,f2079])).
% 6.88/1.42  fof(f2079,plain,(
% 6.88/1.42    ( ! [X152,X151,X149,X150,X148] : (k3_enumset1(k4_tarski(k4_tarski(X148,X149),X151),k4_tarski(k4_tarski(X148,X149),X151),k4_tarski(k4_tarski(X148,X149),X152),k4_tarski(k4_tarski(X150,X149),X151),k4_tarski(k4_tarski(X150,X149),X152)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X148,X148,X148,X148,X150),k3_enumset1(X149,X149,X149,X149,X149)),k3_enumset1(X151,X151,X151,X151,X152))) ) | (~spl5_12 | ~spl5_35)),
% 6.88/1.42    inference(superposition,[],[f831,f151])).
% 6.88/1.42  fof(f151,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) ) | ~spl5_12),
% 6.88/1.42    inference(avatar_component_clause,[],[f150])).
% 6.88/1.42  fof(f150,plain,(
% 6.88/1.42    spl5_12 <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 6.88/1.42  fof(f831,plain,(
% 6.88/1.42    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) ) | ~spl5_35),
% 6.88/1.42    inference(avatar_component_clause,[],[f830])).
% 6.88/1.42  fof(f830,plain,(
% 6.88/1.42    spl5_35 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 6.88/1.42  fof(f4932,plain,(
% 6.88/1.42    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) | (spl5_95 | ~spl5_106)),
% 6.88/1.42    inference(superposition,[],[f2758,f4789])).
% 6.88/1.42  fof(f4789,plain,(
% 6.88/1.42    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | ~spl5_106),
% 6.88/1.42    inference(avatar_component_clause,[],[f4788])).
% 6.88/1.42  fof(f4788,plain,(
% 6.88/1.42    spl5_106 <=> ! [X40,X42,X41,X43,X39] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 6.88/1.42  fof(f2758,plain,(
% 6.88/1.42    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) | spl5_95),
% 6.88/1.42    inference(avatar_component_clause,[],[f2756])).
% 6.88/1.42  fof(f2756,plain,(
% 6.88/1.42    spl5_95 <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 6.88/1.42  fof(f4790,plain,(
% 6.88/1.42    spl5_106 | ~spl5_32 | ~spl5_41),
% 6.88/1.42    inference(avatar_split_clause,[],[f4765,f854,f610,f4788])).
% 6.88/1.42  fof(f610,plain,(
% 6.88/1.42    spl5_32 <=> ! [X16,X13,X15,X12,X14] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 6.88/1.42  fof(f854,plain,(
% 6.88/1.42    spl5_41 <=> ! [X27,X29,X26,X28,X30] : k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 6.88/1.42  fof(f4765,plain,(
% 6.88/1.42    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | (~spl5_32 | ~spl5_41)),
% 6.88/1.42    inference(superposition,[],[f855,f611])).
% 6.88/1.42  fof(f611,plain,(
% 6.88/1.42    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | ~spl5_32),
% 6.88/1.42    inference(avatar_component_clause,[],[f610])).
% 6.88/1.42  fof(f855,plain,(
% 6.88/1.42    ( ! [X30,X28,X26,X29,X27] : (k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))) ) | ~spl5_41),
% 6.88/1.42    inference(avatar_component_clause,[],[f854])).
% 6.88/1.42  fof(f2759,plain,(
% 6.88/1.42    ~spl5_95),
% 6.88/1.42    inference(avatar_split_clause,[],[f37,f2756])).
% 6.88/1.42  fof(f37,plain,(
% 6.88/1.42    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 6.88/1.42    inference(definition_unfolding,[],[f18,f23,f33,f34,f33,f29,f25,f25,f25,f25])).
% 6.88/1.42  fof(f25,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f11])).
% 6.88/1.42  fof(f11,axiom,(
% 6.88/1.42    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 6.88/1.42  fof(f29,plain,(
% 6.88/1.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f7])).
% 6.88/1.42  fof(f7,axiom,(
% 6.88/1.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.88/1.42  fof(f34,plain,(
% 6.88/1.42    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.88/1.42    inference(definition_unfolding,[],[f19,f33])).
% 6.88/1.42  fof(f19,plain,(
% 6.88/1.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f4])).
% 6.88/1.42  fof(f4,axiom,(
% 6.88/1.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 6.88/1.42  fof(f33,plain,(
% 6.88/1.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.88/1.42    inference(definition_unfolding,[],[f21,f32])).
% 6.88/1.42  fof(f32,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.88/1.42    inference(definition_unfolding,[],[f24,f29])).
% 6.88/1.42  fof(f24,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f6])).
% 6.88/1.42  fof(f6,axiom,(
% 6.88/1.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.88/1.42  fof(f21,plain,(
% 6.88/1.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f5])).
% 6.88/1.42  fof(f5,axiom,(
% 6.88/1.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.88/1.42  fof(f23,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f12])).
% 6.88/1.42  fof(f12,axiom,(
% 6.88/1.42    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 6.88/1.42  fof(f18,plain,(
% 6.88/1.42    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 6.88/1.42    inference(cnf_transformation,[],[f17])).
% 6.88/1.42  fof(f17,plain,(
% 6.88/1.42    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 6.88/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 6.88/1.42  fof(f16,plain,(
% 6.88/1.42    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 6.88/1.42    introduced(choice_axiom,[])).
% 6.88/1.42  fof(f15,plain,(
% 6.88/1.42    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 6.88/1.42    inference(ennf_transformation,[],[f14])).
% 6.88/1.42  fof(f14,negated_conjecture,(
% 6.88/1.42    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 6.88/1.42    inference(negated_conjecture,[],[f13])).
% 6.88/1.42  fof(f13,conjecture,(
% 6.88/1.42    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 6.88/1.42  fof(f856,plain,(
% 6.88/1.42    spl5_41 | ~spl5_13 | ~spl5_17),
% 6.88/1.42    inference(avatar_split_clause,[],[f211,f186,f154,f854])).
% 6.88/1.42  fof(f154,plain,(
% 6.88/1.42    spl5_13 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 6.88/1.42  fof(f186,plain,(
% 6.88/1.42    spl5_17 <=> ! [X11,X10,X12] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 6.88/1.42  fof(f211,plain,(
% 6.88/1.42    ( ! [X30,X28,X26,X29,X27] : (k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))) ) | (~spl5_13 | ~spl5_17)),
% 6.88/1.42    inference(superposition,[],[f155,f187])).
% 6.88/1.42  fof(f187,plain,(
% 6.88/1.42    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | ~spl5_17),
% 6.88/1.42    inference(avatar_component_clause,[],[f186])).
% 6.88/1.42  fof(f155,plain,(
% 6.88/1.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_13),
% 6.88/1.42    inference(avatar_component_clause,[],[f154])).
% 6.88/1.42  fof(f832,plain,(
% 6.88/1.42    spl5_35),
% 6.88/1.42    inference(avatar_split_clause,[],[f42,f830])).
% 6.88/1.42  fof(f42,plain,(
% 6.88/1.42    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 6.88/1.42    inference(definition_unfolding,[],[f30,f33,f33,f29])).
% 6.88/1.42  fof(f30,plain,(
% 6.88/1.42    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 6.88/1.42    inference(cnf_transformation,[],[f9])).
% 6.88/1.42  fof(f9,axiom,(
% 6.88/1.42    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 6.88/1.42  fof(f612,plain,(
% 6.88/1.42    spl5_32 | ~spl5_7 | ~spl5_13),
% 6.88/1.42    inference(avatar_split_clause,[],[f172,f154,f90,f610])).
% 6.88/1.42  fof(f90,plain,(
% 6.88/1.42    spl5_7 <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.88/1.42  fof(f172,plain,(
% 6.88/1.42    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | (~spl5_7 | ~spl5_13)),
% 6.88/1.42    inference(superposition,[],[f155,f91])).
% 6.88/1.42  fof(f91,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | ~spl5_7),
% 6.88/1.42    inference(avatar_component_clause,[],[f90])).
% 6.88/1.42  fof(f188,plain,(
% 6.88/1.42    spl5_17 | ~spl5_6 | ~spl5_13),
% 6.88/1.42    inference(avatar_split_clause,[],[f174,f154,f70,f186])).
% 6.88/1.42  fof(f70,plain,(
% 6.88/1.42    spl5_6 <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.88/1.42  fof(f174,plain,(
% 6.88/1.42    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | (~spl5_6 | ~spl5_13)),
% 6.88/1.42    inference(superposition,[],[f155,f71])).
% 6.88/1.42  fof(f71,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) ) | ~spl5_6),
% 6.88/1.42    inference(avatar_component_clause,[],[f70])).
% 6.88/1.42  fof(f156,plain,(
% 6.88/1.42    spl5_13 | ~spl5_2 | ~spl5_5),
% 6.88/1.42    inference(avatar_split_clause,[],[f73,f66,f48,f154])).
% 6.88/1.42  fof(f48,plain,(
% 6.88/1.42    spl5_2 <=> ! [X1,X0] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.88/1.42  fof(f66,plain,(
% 6.88/1.42    spl5_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))),
% 6.88/1.42    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 6.88/1.42  fof(f73,plain,(
% 6.88/1.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | (~spl5_2 | ~spl5_5)),
% 6.88/1.42    inference(superposition,[],[f67,f49])).
% 6.88/1.42  fof(f49,plain,(
% 6.88/1.42    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) ) | ~spl5_2),
% 6.88/1.42    inference(avatar_component_clause,[],[f48])).
% 6.88/1.42  fof(f67,plain,(
% 6.88/1.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_5),
% 6.88/1.42    inference(avatar_component_clause,[],[f66])).
% 6.88/1.42  fof(f152,plain,(
% 6.88/1.42    spl5_12),
% 6.88/1.42    inference(avatar_split_clause,[],[f40,f150])).
% 6.88/1.42  fof(f40,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 6.88/1.42    inference(definition_unfolding,[],[f28,f33,f34,f33])).
% 6.88/1.42  fof(f28,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 6.88/1.42    inference(cnf_transformation,[],[f10])).
% 6.88/1.42  fof(f10,axiom,(
% 6.88/1.42    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 6.88/1.42  fof(f92,plain,(
% 6.88/1.42    spl5_7 | ~spl5_5 | ~spl5_6),
% 6.88/1.42    inference(avatar_split_clause,[],[f83,f70,f66,f90])).
% 6.88/1.42  fof(f83,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | (~spl5_5 | ~spl5_6)),
% 6.88/1.42    inference(superposition,[],[f71,f67])).
% 6.88/1.42  fof(f72,plain,(
% 6.88/1.42    spl5_6),
% 6.88/1.42    inference(avatar_split_clause,[],[f39,f70])).
% 6.88/1.42  fof(f39,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 6.88/1.42    inference(definition_unfolding,[],[f26,f32,f33,f34])).
% 6.88/1.42  fof(f26,plain,(
% 6.88/1.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 6.88/1.42    inference(cnf_transformation,[],[f2])).
% 6.88/1.42  fof(f2,axiom,(
% 6.88/1.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 6.88/1.42  fof(f68,plain,(
% 6.88/1.42    spl5_5),
% 6.88/1.42    inference(avatar_split_clause,[],[f36,f66])).
% 6.88/1.42  fof(f36,plain,(
% 6.88/1.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) )),
% 6.88/1.42    inference(definition_unfolding,[],[f31,f33,f32])).
% 6.88/1.42  fof(f31,plain,(
% 6.88/1.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 6.88/1.42    inference(cnf_transformation,[],[f3])).
% 6.88/1.42  fof(f3,axiom,(
% 6.88/1.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 6.88/1.42  fof(f50,plain,(
% 6.88/1.42    spl5_2),
% 6.88/1.42    inference(avatar_split_clause,[],[f38,f48])).
% 6.88/1.42  fof(f38,plain,(
% 6.88/1.42    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 6.88/1.42    inference(definition_unfolding,[],[f20,f33,f33])).
% 6.88/1.42  fof(f20,plain,(
% 6.88/1.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.88/1.42    inference(cnf_transformation,[],[f1])).
% 6.88/1.42  fof(f1,axiom,(
% 6.88/1.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.88/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.88/1.42  % SZS output end Proof for theBenchmark
% 6.88/1.42  % (21032)------------------------------
% 6.88/1.42  % (21032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.88/1.42  % (21032)Termination reason: Refutation
% 6.88/1.42  
% 6.88/1.42  % (21032)Memory used [KB]: 12153
% 6.88/1.42  % (21032)Time elapsed: 0.764 s
% 6.88/1.42  % (21032)------------------------------
% 6.88/1.42  % (21032)------------------------------
% 6.88/1.42  % (20833)Success in time 1.067 s
%------------------------------------------------------------------------------
