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
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 7.10s
% Output     : Refutation 7.10s
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
    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f156,f188,f415,f612,f832,f856,f2759,f4790,f4936])).

fof(f4936,plain,
    ( ~ spl5_24
    | ~ spl5_35
    | spl5_95
    | ~ spl5_106 ),
    inference(avatar_contradiction_clause,[],[f4935])).

fof(f4935,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_35
    | spl5_95
    | ~ spl5_106 ),
    inference(subsumption_resolution,[],[f4932,f2080])).

fof(f2080,plain,
    ( ! [X156,X154,X157,X155,X153] : k3_enumset1(k4_tarski(k4_tarski(X153,X154),X156),k4_tarski(k4_tarski(X153,X154),X156),k4_tarski(k4_tarski(X153,X154),X157),k4_tarski(k4_tarski(X153,X155),X156),k4_tarski(k4_tarski(X153,X155),X157)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X153,X153,X153,X153,X153),k3_enumset1(X154,X154,X154,X154,X155)),k3_enumset1(X156,X156,X156,X156,X157))
    | ~ spl5_24
    | ~ spl5_35 ),
    inference(superposition,[],[f831,f414])).

fof(f414,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f831,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl5_35
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f4932,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))
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
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_95 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f2756,plain,
    ( spl5_95
  <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
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
    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f18,f23,f34,f33,f33,f29,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

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

fof(f415,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f41,f413])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f27,f34,f33,f33])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9688)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (9696)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (9691)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (9686)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (9701)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (9687)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (9692)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (9700)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (9690)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (9695)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (9703)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (9698)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (9693)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (9694)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (9689)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (9697)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (9704)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (9702)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (9697)Refutation not found, incomplete strategy% (9697)------------------------------
% 0.22/0.51  % (9697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9697)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9697)Memory used [KB]: 10618
% 0.22/0.51  % (9697)Time elapsed: 0.086 s
% 0.22/0.51  % (9697)------------------------------
% 0.22/0.51  % (9697)------------------------------
% 5.31/1.07  % (9690)Time limit reached!
% 5.31/1.07  % (9690)------------------------------
% 5.31/1.07  % (9690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.31/1.07  % (9690)Termination reason: Time limit
% 5.31/1.07  % (9690)Termination phase: Saturation
% 5.31/1.07  
% 5.31/1.07  % (9690)Memory used [KB]: 10746
% 5.31/1.07  % (9690)Time elapsed: 0.627 s
% 5.31/1.07  % (9690)------------------------------
% 5.31/1.07  % (9690)------------------------------
% 7.10/1.30  % (9693)Refutation found. Thanks to Tanya!
% 7.10/1.30  % SZS status Theorem for theBenchmark
% 7.10/1.30  % SZS output start Proof for theBenchmark
% 7.10/1.30  fof(f4937,plain,(
% 7.10/1.30    $false),
% 7.10/1.30    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f156,f188,f415,f612,f832,f856,f2759,f4790,f4936])).
% 7.10/1.30  fof(f4936,plain,(
% 7.10/1.30    ~spl5_24 | ~spl5_35 | spl5_95 | ~spl5_106),
% 7.10/1.30    inference(avatar_contradiction_clause,[],[f4935])).
% 7.10/1.30  fof(f4935,plain,(
% 7.10/1.30    $false | (~spl5_24 | ~spl5_35 | spl5_95 | ~spl5_106)),
% 7.10/1.30    inference(subsumption_resolution,[],[f4932,f2080])).
% 7.10/1.30  fof(f2080,plain,(
% 7.10/1.30    ( ! [X156,X154,X157,X155,X153] : (k3_enumset1(k4_tarski(k4_tarski(X153,X154),X156),k4_tarski(k4_tarski(X153,X154),X156),k4_tarski(k4_tarski(X153,X154),X157),k4_tarski(k4_tarski(X153,X155),X156),k4_tarski(k4_tarski(X153,X155),X157)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X153,X153,X153,X153,X153),k3_enumset1(X154,X154,X154,X154,X155)),k3_enumset1(X156,X156,X156,X156,X157))) ) | (~spl5_24 | ~spl5_35)),
% 7.10/1.30    inference(superposition,[],[f831,f414])).
% 7.10/1.30  fof(f414,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) ) | ~spl5_24),
% 7.10/1.30    inference(avatar_component_clause,[],[f413])).
% 7.10/1.30  fof(f413,plain,(
% 7.10/1.30    spl5_24 <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 7.10/1.30  fof(f831,plain,(
% 7.10/1.30    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) ) | ~spl5_35),
% 7.10/1.30    inference(avatar_component_clause,[],[f830])).
% 7.10/1.30  fof(f830,plain,(
% 7.10/1.30    spl5_35 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 7.10/1.30  fof(f4932,plain,(
% 7.10/1.30    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) | (spl5_95 | ~spl5_106)),
% 7.10/1.30    inference(superposition,[],[f2758,f4789])).
% 7.10/1.30  fof(f4789,plain,(
% 7.10/1.30    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | ~spl5_106),
% 7.10/1.30    inference(avatar_component_clause,[],[f4788])).
% 7.10/1.30  fof(f4788,plain,(
% 7.10/1.30    spl5_106 <=> ! [X40,X42,X41,X43,X39] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 7.10/1.30  fof(f2758,plain,(
% 7.10/1.30    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_95),
% 7.10/1.30    inference(avatar_component_clause,[],[f2756])).
% 7.10/1.30  fof(f2756,plain,(
% 7.10/1.30    spl5_95 <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 7.10/1.30  fof(f4790,plain,(
% 7.10/1.30    spl5_106 | ~spl5_32 | ~spl5_41),
% 7.10/1.30    inference(avatar_split_clause,[],[f4765,f854,f610,f4788])).
% 7.10/1.30  fof(f610,plain,(
% 7.10/1.30    spl5_32 <=> ! [X16,X13,X15,X12,X14] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 7.10/1.30  fof(f854,plain,(
% 7.10/1.30    spl5_41 <=> ! [X27,X29,X26,X28,X30] : k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 7.10/1.30  fof(f4765,plain,(
% 7.10/1.30    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | (~spl5_32 | ~spl5_41)),
% 7.10/1.30    inference(superposition,[],[f855,f611])).
% 7.10/1.30  fof(f611,plain,(
% 7.10/1.30    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | ~spl5_32),
% 7.10/1.30    inference(avatar_component_clause,[],[f610])).
% 7.10/1.30  fof(f855,plain,(
% 7.10/1.30    ( ! [X30,X28,X26,X29,X27] : (k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))) ) | ~spl5_41),
% 7.10/1.30    inference(avatar_component_clause,[],[f854])).
% 7.10/1.30  fof(f2759,plain,(
% 7.10/1.30    ~spl5_95),
% 7.10/1.30    inference(avatar_split_clause,[],[f37,f2756])).
% 7.10/1.30  fof(f37,plain,(
% 7.10/1.30    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 7.10/1.30    inference(definition_unfolding,[],[f18,f23,f34,f33,f33,f29,f25,f25,f25,f25])).
% 7.10/1.30  fof(f25,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f11])).
% 7.10/1.30  fof(f11,axiom,(
% 7.10/1.30    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 7.10/1.30  fof(f29,plain,(
% 7.10/1.30    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f7])).
% 7.10/1.30  fof(f7,axiom,(
% 7.10/1.30    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 7.10/1.30  fof(f33,plain,(
% 7.10/1.30    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.10/1.30    inference(definition_unfolding,[],[f21,f32])).
% 7.10/1.30  fof(f32,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.10/1.30    inference(definition_unfolding,[],[f24,f29])).
% 7.10/1.30  fof(f24,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f6])).
% 7.10/1.30  fof(f6,axiom,(
% 7.10/1.30    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.10/1.30  fof(f21,plain,(
% 7.10/1.30    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f5])).
% 7.10/1.30  fof(f5,axiom,(
% 7.10/1.30    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.10/1.30  fof(f34,plain,(
% 7.10/1.30    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.10/1.30    inference(definition_unfolding,[],[f19,f33])).
% 7.10/1.30  fof(f19,plain,(
% 7.10/1.30    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f4])).
% 7.10/1.30  fof(f4,axiom,(
% 7.10/1.30    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.10/1.30  fof(f23,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f12])).
% 7.10/1.30  fof(f12,axiom,(
% 7.10/1.30    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 7.10/1.30  fof(f18,plain,(
% 7.10/1.30    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 7.10/1.30    inference(cnf_transformation,[],[f17])).
% 7.10/1.30  fof(f17,plain,(
% 7.10/1.30    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 7.10/1.30    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 7.10/1.30  fof(f16,plain,(
% 7.10/1.30    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 7.10/1.30    introduced(choice_axiom,[])).
% 7.10/1.30  fof(f15,plain,(
% 7.10/1.30    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 7.10/1.30    inference(ennf_transformation,[],[f14])).
% 7.10/1.30  fof(f14,negated_conjecture,(
% 7.10/1.30    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 7.10/1.30    inference(negated_conjecture,[],[f13])).
% 7.10/1.30  fof(f13,conjecture,(
% 7.10/1.30    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 7.10/1.30  fof(f856,plain,(
% 7.10/1.30    spl5_41 | ~spl5_13 | ~spl5_17),
% 7.10/1.30    inference(avatar_split_clause,[],[f211,f186,f154,f854])).
% 7.10/1.30  fof(f154,plain,(
% 7.10/1.30    spl5_13 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 7.10/1.30  fof(f186,plain,(
% 7.10/1.30    spl5_17 <=> ! [X11,X10,X12] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 7.10/1.30  fof(f211,plain,(
% 7.10/1.30    ( ! [X30,X28,X26,X29,X27] : (k3_enumset1(X29,X30,X26,X27,X28) = k2_xboole_0(k3_enumset1(X30,X30,X30,X30,X29),k3_enumset1(X27,X26,X28,X28,X28))) ) | (~spl5_13 | ~spl5_17)),
% 7.10/1.30    inference(superposition,[],[f155,f187])).
% 7.10/1.30  fof(f187,plain,(
% 7.10/1.30    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | ~spl5_17),
% 7.10/1.30    inference(avatar_component_clause,[],[f186])).
% 7.10/1.30  fof(f155,plain,(
% 7.10/1.30    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_13),
% 7.10/1.30    inference(avatar_component_clause,[],[f154])).
% 7.10/1.30  fof(f832,plain,(
% 7.10/1.30    spl5_35),
% 7.10/1.30    inference(avatar_split_clause,[],[f42,f830])).
% 7.10/1.30  fof(f42,plain,(
% 7.10/1.30    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 7.10/1.30    inference(definition_unfolding,[],[f30,f33,f33,f29])).
% 7.10/1.30  fof(f30,plain,(
% 7.10/1.30    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 7.10/1.30    inference(cnf_transformation,[],[f9])).
% 7.10/1.30  fof(f9,axiom,(
% 7.10/1.30    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 7.10/1.30  fof(f612,plain,(
% 7.10/1.30    spl5_32 | ~spl5_7 | ~spl5_13),
% 7.10/1.30    inference(avatar_split_clause,[],[f172,f154,f90,f610])).
% 7.10/1.30  fof(f90,plain,(
% 7.10/1.30    spl5_7 <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 7.10/1.30  fof(f172,plain,(
% 7.10/1.30    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | (~spl5_7 | ~spl5_13)),
% 7.10/1.30    inference(superposition,[],[f155,f91])).
% 7.10/1.30  fof(f91,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | ~spl5_7),
% 7.10/1.30    inference(avatar_component_clause,[],[f90])).
% 7.10/1.30  fof(f415,plain,(
% 7.10/1.30    spl5_24),
% 7.10/1.30    inference(avatar_split_clause,[],[f41,f413])).
% 7.10/1.30  fof(f41,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 7.10/1.30    inference(definition_unfolding,[],[f27,f34,f33,f33])).
% 7.10/1.30  fof(f27,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 7.10/1.30    inference(cnf_transformation,[],[f10])).
% 7.10/1.30  fof(f10,axiom,(
% 7.10/1.30    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 7.10/1.30  fof(f188,plain,(
% 7.10/1.30    spl5_17 | ~spl5_6 | ~spl5_13),
% 7.10/1.30    inference(avatar_split_clause,[],[f174,f154,f70,f186])).
% 7.10/1.30  fof(f70,plain,(
% 7.10/1.30    spl5_6 <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 7.10/1.30  fof(f174,plain,(
% 7.10/1.30    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | (~spl5_6 | ~spl5_13)),
% 7.10/1.30    inference(superposition,[],[f155,f71])).
% 7.10/1.30  fof(f71,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) ) | ~spl5_6),
% 7.10/1.30    inference(avatar_component_clause,[],[f70])).
% 7.10/1.30  fof(f156,plain,(
% 7.10/1.30    spl5_13 | ~spl5_2 | ~spl5_5),
% 7.10/1.30    inference(avatar_split_clause,[],[f73,f66,f48,f154])).
% 7.10/1.30  fof(f48,plain,(
% 7.10/1.30    spl5_2 <=> ! [X1,X0] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 7.10/1.30  fof(f66,plain,(
% 7.10/1.30    spl5_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))),
% 7.10/1.30    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 7.10/1.30  fof(f73,plain,(
% 7.10/1.30    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | (~spl5_2 | ~spl5_5)),
% 7.10/1.30    inference(superposition,[],[f67,f49])).
% 7.10/1.30  fof(f49,plain,(
% 7.10/1.30    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) ) | ~spl5_2),
% 7.10/1.30    inference(avatar_component_clause,[],[f48])).
% 7.10/1.30  fof(f67,plain,(
% 7.10/1.30    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_5),
% 7.10/1.30    inference(avatar_component_clause,[],[f66])).
% 7.10/1.30  fof(f92,plain,(
% 7.10/1.30    spl5_7 | ~spl5_5 | ~spl5_6),
% 7.10/1.30    inference(avatar_split_clause,[],[f83,f70,f66,f90])).
% 7.10/1.30  fof(f83,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | (~spl5_5 | ~spl5_6)),
% 7.10/1.30    inference(superposition,[],[f71,f67])).
% 7.10/1.30  fof(f72,plain,(
% 7.10/1.30    spl5_6),
% 7.10/1.30    inference(avatar_split_clause,[],[f39,f70])).
% 7.10/1.30  fof(f39,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 7.10/1.30    inference(definition_unfolding,[],[f26,f32,f33,f34])).
% 7.10/1.30  fof(f26,plain,(
% 7.10/1.30    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 7.10/1.30    inference(cnf_transformation,[],[f2])).
% 7.10/1.30  fof(f2,axiom,(
% 7.10/1.30    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 7.10/1.30  fof(f68,plain,(
% 7.10/1.30    spl5_5),
% 7.10/1.30    inference(avatar_split_clause,[],[f36,f66])).
% 7.10/1.30  fof(f36,plain,(
% 7.10/1.30    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) )),
% 7.10/1.30    inference(definition_unfolding,[],[f31,f33,f32])).
% 7.10/1.30  fof(f31,plain,(
% 7.10/1.30    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 7.10/1.30    inference(cnf_transformation,[],[f3])).
% 7.10/1.30  fof(f3,axiom,(
% 7.10/1.30    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 7.10/1.30  fof(f50,plain,(
% 7.10/1.30    spl5_2),
% 7.10/1.30    inference(avatar_split_clause,[],[f38,f48])).
% 7.10/1.30  fof(f38,plain,(
% 7.10/1.30    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.10/1.30    inference(definition_unfolding,[],[f20,f33,f33])).
% 7.10/1.30  fof(f20,plain,(
% 7.10/1.30    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.10/1.30    inference(cnf_transformation,[],[f1])).
% 7.10/1.30  fof(f1,axiom,(
% 7.10/1.30    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.10/1.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 7.10/1.30  % SZS output end Proof for theBenchmark
% 7.10/1.30  % (9693)------------------------------
% 7.10/1.30  % (9693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.10/1.30  % (9693)Termination reason: Refutation
% 7.10/1.30  
% 7.10/1.30  % (9693)Memory used [KB]: 12153
% 7.10/1.30  % (9693)Time elapsed: 0.814 s
% 7.10/1.30  % (9693)------------------------------
% 7.10/1.30  % (9693)------------------------------
% 7.10/1.30  % (9684)Success in time 0.939 s
%------------------------------------------------------------------------------
