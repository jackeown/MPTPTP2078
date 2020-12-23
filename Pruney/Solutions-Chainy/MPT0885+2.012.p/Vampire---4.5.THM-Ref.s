%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 5.70s
% Output     : Refutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 232 expanded)
%              Number of leaves         :   25 (  98 expanded)
%              Depth                    :    7
%              Number of atoms          :  145 ( 325 expanded)
%              Number of equality atoms :   71 ( 219 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f156,f188,f417,f616,f773,f918,f2369,f7015,f7229])).

fof(f7229,plain,
    ( ~ spl5_24
    | ~ spl5_35
    | spl5_100
    | ~ spl5_132 ),
    inference(avatar_contradiction_clause,[],[f7228])).

fof(f7228,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_35
    | spl5_100
    | ~ spl5_132 ),
    inference(subsumption_resolution,[],[f7225,f1462])).

fof(f1462,plain,
    ( ! [X125,X123,X121,X124,X122] : k3_enumset1(k4_tarski(k4_tarski(X121,X122),X124),k4_tarski(k4_tarski(X121,X122),X124),k4_tarski(k4_tarski(X121,X122),X125),k4_tarski(k4_tarski(X121,X123),X124),k4_tarski(k4_tarski(X121,X123),X125)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X121,X121,X121,X121,X121),k3_enumset1(X122,X122,X122,X122,X123)),k3_enumset1(X124,X124,X124,X124,X125))
    | ~ spl5_24
    | ~ spl5_35 ),
    inference(superposition,[],[f772,f416])).

fof(f416,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f772,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl5_35
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f7225,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_100
    | ~ spl5_132 ),
    inference(superposition,[],[f2368,f7014])).

fof(f7014,plain,
    ( ! [X39,X43,X41,X42,X40] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f7013])).

fof(f7013,plain,
    ( spl5_132
  <=> ! [X40,X42,X41,X43,X39] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f2368,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_100 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f2366,plain,
    ( spl5_100
  <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f7015,plain,
    ( spl5_132
    | ~ spl5_32
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f6990,f916,f614,f7013])).

fof(f614,plain,
    ( spl5_32
  <=> ! [X16,X13,X15,X12,X14] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f916,plain,
    ( spl5_43
  <=> ! [X25,X27,X24,X26,X28] : k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f6990,plain,
    ( ! [X39,X43,X41,X42,X40] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)
    | ~ spl5_32
    | ~ spl5_43 ),
    inference(superposition,[],[f917,f615])).

fof(f615,plain,
    ( ! [X14,X12,X15,X13,X16] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f614])).

fof(f917,plain,
    ( ! [X28,X26,X24,X27,X25] : k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f916])).

fof(f2369,plain,(
    ~ spl5_100 ),
    inference(avatar_split_clause,[],[f37,f2366])).

fof(f37,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f18,f23,f34,f33,f33,f28,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f24,f28])).

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

fof(f918,plain,
    ( spl5_43
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f210,f186,f154,f916])).

fof(f154,plain,
    ( spl5_13
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f186,plain,
    ( spl5_17
  <=> ! [X11,X10,X12] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f210,plain,
    ( ! [X28,X26,X24,X27,X25] : k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26))
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

fof(f773,plain,(
    spl5_35 ),
    inference(avatar_split_clause,[],[f42,f771])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f30,f33,f33,f28])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f616,plain,
    ( spl5_32
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f172,f154,f90,f614])).

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

fof(f417,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f40,f415])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f26,f34,f33,f33])).

fof(f26,plain,(
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
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f174,plain,
    ( ! [X12,X10,X11] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(superposition,[],[f155,f71])).

fof(f71,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))
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
    inference(avatar_split_clause,[],[f41,f70])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f29,f28,f32,f34])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (3496)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.44  % (3496)Refutation not found, incomplete strategy% (3496)------------------------------
% 0.22/0.44  % (3496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (3496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.44  
% 0.22/0.44  % (3496)Memory used [KB]: 10618
% 0.22/0.44  % (3496)Time elapsed: 0.004 s
% 0.22/0.44  % (3496)------------------------------
% 0.22/0.44  % (3496)------------------------------
% 0.22/0.44  % (3495)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (3488)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (3489)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (3494)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (3497)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (3491)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (3493)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (3502)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (3485)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (3499)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (3498)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (3490)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (3501)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (3492)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (3487)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (3486)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.54  % (3500)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.38/1.04  % (3489)Time limit reached!
% 5.38/1.04  % (3489)------------------------------
% 5.38/1.04  % (3489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.38/1.04  % (3489)Termination reason: Time limit
% 5.38/1.04  
% 5.38/1.04  % (3489)Memory used [KB]: 11257
% 5.38/1.04  % (3489)Time elapsed: 0.606 s
% 5.38/1.04  % (3489)------------------------------
% 5.38/1.04  % (3489)------------------------------
% 5.70/1.14  % (3492)Refutation found. Thanks to Tanya!
% 5.70/1.14  % SZS status Theorem for theBenchmark
% 6.21/1.15  % SZS output start Proof for theBenchmark
% 6.21/1.15  fof(f7230,plain,(
% 6.21/1.15    $false),
% 6.21/1.15    inference(avatar_sat_refutation,[],[f50,f68,f72,f92,f156,f188,f417,f616,f773,f918,f2369,f7015,f7229])).
% 6.21/1.15  fof(f7229,plain,(
% 6.21/1.15    ~spl5_24 | ~spl5_35 | spl5_100 | ~spl5_132),
% 6.21/1.15    inference(avatar_contradiction_clause,[],[f7228])).
% 6.21/1.15  fof(f7228,plain,(
% 6.21/1.15    $false | (~spl5_24 | ~spl5_35 | spl5_100 | ~spl5_132)),
% 6.21/1.15    inference(subsumption_resolution,[],[f7225,f1462])).
% 6.21/1.15  fof(f1462,plain,(
% 6.21/1.15    ( ! [X125,X123,X121,X124,X122] : (k3_enumset1(k4_tarski(k4_tarski(X121,X122),X124),k4_tarski(k4_tarski(X121,X122),X124),k4_tarski(k4_tarski(X121,X122),X125),k4_tarski(k4_tarski(X121,X123),X124),k4_tarski(k4_tarski(X121,X123),X125)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X121,X121,X121,X121,X121),k3_enumset1(X122,X122,X122,X122,X123)),k3_enumset1(X124,X124,X124,X124,X125))) ) | (~spl5_24 | ~spl5_35)),
% 6.21/1.15    inference(superposition,[],[f772,f416])).
% 6.21/1.15  fof(f416,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) ) | ~spl5_24),
% 6.21/1.15    inference(avatar_component_clause,[],[f415])).
% 6.21/1.15  fof(f415,plain,(
% 6.21/1.15    spl5_24 <=> ! [X1,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 6.21/1.15  fof(f772,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) ) | ~spl5_35),
% 6.21/1.15    inference(avatar_component_clause,[],[f771])).
% 6.21/1.15  fof(f771,plain,(
% 6.21/1.15    spl5_35 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 6.21/1.15  fof(f7225,plain,(
% 6.21/1.15    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) | (spl5_100 | ~spl5_132)),
% 6.21/1.15    inference(superposition,[],[f2368,f7014])).
% 6.21/1.15  fof(f7014,plain,(
% 6.21/1.15    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | ~spl5_132),
% 6.21/1.15    inference(avatar_component_clause,[],[f7013])).
% 6.21/1.15  fof(f7013,plain,(
% 6.21/1.15    spl5_132 <=> ! [X40,X42,X41,X43,X39] : k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).
% 6.21/1.15  fof(f2368,plain,(
% 6.21/1.15    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_100),
% 6.21/1.15    inference(avatar_component_clause,[],[f2366])).
% 6.21/1.15  fof(f2366,plain,(
% 6.21/1.15    spl5_100 <=> k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) = k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 6.21/1.15  fof(f7015,plain,(
% 6.21/1.15    spl5_132 | ~spl5_32 | ~spl5_43),
% 6.21/1.15    inference(avatar_split_clause,[],[f6990,f916,f614,f7013])).
% 6.21/1.15  fof(f614,plain,(
% 6.21/1.15    spl5_32 <=> ! [X16,X13,X15,X12,X14] : k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 6.21/1.15  fof(f916,plain,(
% 6.21/1.15    spl5_43 <=> ! [X25,X27,X24,X26,X28] : k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 6.21/1.15  fof(f6990,plain,(
% 6.21/1.15    ( ! [X39,X43,X41,X42,X40] : (k3_enumset1(X40,X39,X41,X42,X43) = k3_enumset1(X40,X39,X42,X41,X43)) ) | (~spl5_32 | ~spl5_43)),
% 6.21/1.15    inference(superposition,[],[f917,f615])).
% 6.21/1.15  fof(f615,plain,(
% 6.21/1.15    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | ~spl5_32),
% 6.21/1.15    inference(avatar_component_clause,[],[f614])).
% 6.21/1.15  fof(f917,plain,(
% 6.21/1.15    ( ! [X28,X26,X24,X27,X25] : (k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26))) ) | ~spl5_43),
% 6.21/1.15    inference(avatar_component_clause,[],[f916])).
% 6.21/1.15  fof(f2369,plain,(
% 6.21/1.15    ~spl5_100),
% 6.21/1.15    inference(avatar_split_clause,[],[f37,f2366])).
% 6.21/1.15  fof(f37,plain,(
% 6.21/1.15    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 6.21/1.15    inference(definition_unfolding,[],[f18,f23,f34,f33,f33,f28,f25,f25,f25,f25])).
% 6.21/1.15  fof(f25,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f11])).
% 6.21/1.15  fof(f11,axiom,(
% 6.21/1.15    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 6.21/1.15  fof(f28,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f7])).
% 6.21/1.15  fof(f7,axiom,(
% 6.21/1.15    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 6.21/1.15  fof(f33,plain,(
% 6.21/1.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.21/1.15    inference(definition_unfolding,[],[f21,f32])).
% 6.21/1.15  fof(f32,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.21/1.15    inference(definition_unfolding,[],[f24,f28])).
% 6.21/1.15  fof(f24,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f6])).
% 6.21/1.15  fof(f6,axiom,(
% 6.21/1.15    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 6.21/1.15  fof(f21,plain,(
% 6.21/1.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f5])).
% 6.21/1.15  fof(f5,axiom,(
% 6.21/1.15    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.21/1.15  fof(f34,plain,(
% 6.21/1.15    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.21/1.15    inference(definition_unfolding,[],[f19,f33])).
% 6.21/1.15  fof(f19,plain,(
% 6.21/1.15    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f4])).
% 6.21/1.15  fof(f4,axiom,(
% 6.21/1.15    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 6.21/1.15  fof(f23,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f12])).
% 6.21/1.15  fof(f12,axiom,(
% 6.21/1.15    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 6.21/1.15  fof(f18,plain,(
% 6.21/1.15    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 6.21/1.15    inference(cnf_transformation,[],[f17])).
% 6.21/1.15  fof(f17,plain,(
% 6.21/1.15    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 6.21/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 6.21/1.15  fof(f16,plain,(
% 6.21/1.15    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 6.21/1.15    introduced(choice_axiom,[])).
% 6.21/1.15  fof(f15,plain,(
% 6.21/1.15    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 6.21/1.15    inference(ennf_transformation,[],[f14])).
% 6.21/1.15  fof(f14,negated_conjecture,(
% 6.21/1.15    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 6.21/1.15    inference(negated_conjecture,[],[f13])).
% 6.21/1.15  fof(f13,conjecture,(
% 6.21/1.15    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 6.21/1.15  fof(f918,plain,(
% 6.21/1.15    spl5_43 | ~spl5_13 | ~spl5_17),
% 6.21/1.15    inference(avatar_split_clause,[],[f210,f186,f154,f916])).
% 6.21/1.15  fof(f154,plain,(
% 6.21/1.15    spl5_13 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 6.21/1.15  fof(f186,plain,(
% 6.21/1.15    spl5_17 <=> ! [X11,X10,X12] : k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 6.21/1.15  fof(f210,plain,(
% 6.21/1.15    ( ! [X28,X26,X24,X27,X25] : (k3_enumset1(X27,X28,X24,X25,X26) = k2_xboole_0(k3_enumset1(X28,X28,X28,X28,X27),k3_enumset1(X25,X24,X26,X26,X26))) ) | (~spl5_13 | ~spl5_17)),
% 6.21/1.15    inference(superposition,[],[f155,f187])).
% 6.21/1.15  fof(f187,plain,(
% 6.21/1.15    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | ~spl5_17),
% 6.21/1.15    inference(avatar_component_clause,[],[f186])).
% 6.21/1.15  fof(f155,plain,(
% 6.21/1.15    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_13),
% 6.21/1.15    inference(avatar_component_clause,[],[f154])).
% 6.21/1.15  fof(f773,plain,(
% 6.21/1.15    spl5_35),
% 6.21/1.15    inference(avatar_split_clause,[],[f42,f771])).
% 6.21/1.15  fof(f42,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 6.21/1.15    inference(definition_unfolding,[],[f30,f33,f33,f28])).
% 6.21/1.15  fof(f30,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 6.21/1.15    inference(cnf_transformation,[],[f9])).
% 6.21/1.15  fof(f9,axiom,(
% 6.21/1.15    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 6.21/1.15  fof(f616,plain,(
% 6.21/1.15    spl5_32 | ~spl5_7 | ~spl5_13),
% 6.21/1.15    inference(avatar_split_clause,[],[f172,f154,f90,f614])).
% 6.21/1.15  fof(f90,plain,(
% 6.21/1.15    spl5_7 <=> ! [X1,X0,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.21/1.15  fof(f172,plain,(
% 6.21/1.15    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X15,X16,X12,X13,X14) = k2_xboole_0(k3_enumset1(X16,X16,X16,X16,X15),k3_enumset1(X12,X13,X14,X14,X14))) ) | (~spl5_7 | ~spl5_13)),
% 6.21/1.15    inference(superposition,[],[f155,f91])).
% 6.21/1.15  fof(f91,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | ~spl5_7),
% 6.21/1.15    inference(avatar_component_clause,[],[f90])).
% 6.21/1.15  fof(f417,plain,(
% 6.21/1.15    spl5_24),
% 6.21/1.15    inference(avatar_split_clause,[],[f40,f415])).
% 6.21/1.15  fof(f40,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 6.21/1.15    inference(definition_unfolding,[],[f26,f34,f33,f33])).
% 6.21/1.15  fof(f26,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 6.21/1.15    inference(cnf_transformation,[],[f10])).
% 6.21/1.15  fof(f10,axiom,(
% 6.21/1.15    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 6.21/1.15  fof(f188,plain,(
% 6.21/1.15    spl5_17 | ~spl5_6 | ~spl5_13),
% 6.21/1.15    inference(avatar_split_clause,[],[f174,f154,f70,f186])).
% 6.21/1.15  fof(f70,plain,(
% 6.21/1.15    spl5_6 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.21/1.15  fof(f174,plain,(
% 6.21/1.15    ( ! [X12,X10,X11] : (k3_enumset1(X10,X10,X10,X11,X12) = k3_enumset1(X11,X10,X12,X12,X12)) ) | (~spl5_6 | ~spl5_13)),
% 6.21/1.15    inference(superposition,[],[f155,f71])).
% 6.21/1.15  fof(f71,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))) ) | ~spl5_6),
% 6.21/1.15    inference(avatar_component_clause,[],[f70])).
% 6.21/1.15  fof(f156,plain,(
% 6.21/1.15    spl5_13 | ~spl5_2 | ~spl5_5),
% 6.21/1.15    inference(avatar_split_clause,[],[f73,f66,f48,f154])).
% 6.21/1.15  fof(f48,plain,(
% 6.21/1.15    spl5_2 <=> ! [X1,X0] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.21/1.15  fof(f66,plain,(
% 6.21/1.15    spl5_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))),
% 6.21/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 6.21/1.15  fof(f73,plain,(
% 6.21/1.15    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X3,X4))) ) | (~spl5_2 | ~spl5_5)),
% 6.21/1.15    inference(superposition,[],[f67,f49])).
% 6.21/1.15  fof(f49,plain,(
% 6.21/1.15    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) ) | ~spl5_2),
% 6.21/1.15    inference(avatar_component_clause,[],[f48])).
% 6.21/1.15  fof(f67,plain,(
% 6.21/1.15    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) ) | ~spl5_5),
% 6.21/1.15    inference(avatar_component_clause,[],[f66])).
% 6.21/1.15  fof(f92,plain,(
% 6.21/1.15    spl5_7 | ~spl5_5 | ~spl5_6),
% 6.21/1.15    inference(avatar_split_clause,[],[f83,f70,f66,f90])).
% 6.21/1.15  fof(f83,plain,(
% 6.21/1.15    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) ) | (~spl5_5 | ~spl5_6)),
% 6.21/1.15    inference(superposition,[],[f71,f67])).
% 6.21/1.15  fof(f72,plain,(
% 6.21/1.15    spl5_6),
% 6.21/1.15    inference(avatar_split_clause,[],[f41,f70])).
% 6.21/1.15  fof(f41,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))) )),
% 6.21/1.15    inference(definition_unfolding,[],[f29,f28,f32,f34])).
% 6.21/1.15  fof(f29,plain,(
% 6.21/1.15    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 6.21/1.15    inference(cnf_transformation,[],[f2])).
% 6.21/1.15  fof(f2,axiom,(
% 6.21/1.15    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 6.21/1.15  fof(f68,plain,(
% 6.21/1.15    spl5_5),
% 6.21/1.15    inference(avatar_split_clause,[],[f36,f66])).
% 6.21/1.15  fof(f36,plain,(
% 6.21/1.15    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) )),
% 6.21/1.15    inference(definition_unfolding,[],[f31,f33,f32])).
% 6.21/1.15  fof(f31,plain,(
% 6.21/1.15    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 6.21/1.15    inference(cnf_transformation,[],[f3])).
% 6.21/1.15  fof(f3,axiom,(
% 6.21/1.15    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 6.21/1.15  fof(f50,plain,(
% 6.21/1.15    spl5_2),
% 6.21/1.15    inference(avatar_split_clause,[],[f38,f48])).
% 6.21/1.15  fof(f38,plain,(
% 6.21/1.15    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 6.21/1.15    inference(definition_unfolding,[],[f20,f33,f33])).
% 6.21/1.15  fof(f20,plain,(
% 6.21/1.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.21/1.15    inference(cnf_transformation,[],[f1])).
% 6.21/1.15  fof(f1,axiom,(
% 6.21/1.15    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.21/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.21/1.15  % SZS output end Proof for theBenchmark
% 6.21/1.15  % (3492)------------------------------
% 6.21/1.15  % (3492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.21/1.15  % (3492)Termination reason: Refutation
% 6.21/1.15  
% 6.21/1.15  % (3492)Memory used [KB]: 13560
% 6.21/1.15  % (3492)Time elapsed: 0.682 s
% 6.21/1.15  % (3492)------------------------------
% 6.21/1.15  % (3492)------------------------------
% 6.21/1.15  % (3484)Success in time 0.792 s
%------------------------------------------------------------------------------
