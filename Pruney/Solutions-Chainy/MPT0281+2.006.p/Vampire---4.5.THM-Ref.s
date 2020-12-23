%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:38 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 168 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 351 expanded)
%              Number of equality atoms :   26 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f107,f120,f171,f213,f228,f255])).

fof(f255,plain,
    ( ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f10,f241,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f241,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f105,f208])).

fof(f208,plain,
    ( sK1 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_8
  <=> sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f105,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_4
  <=> r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f10,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f228,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f35,f224,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f224,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | spl4_9 ),
    inference(resolution,[],[f212,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(sK0,sK1)))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f9,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f212,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_9
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f213,plain,
    ( spl4_8
    | ~ spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f202,f87,f210,f206])).

fof(f87,plain,
    ( spl4_1
  <=> r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f202,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))
    | sK1 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f201,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f201,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f89,f37])).

fof(f89,plain,
    ( r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f171,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f10,f165,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f165,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f163,f35])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f127,f38])).

fof(f127,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_zfmisc_1(sK1))
        | r1_tarski(X6,sK0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f59,f102])).

fof(f102,plain,
    ( sK0 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_3
  <=> sK0 = k3_tarski(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f35,f116,f38])).

fof(f116,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl4_4 ),
    inference(resolution,[],[f106,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(sK0,sK1)))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f11])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f106,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f96,f91,f104,f100])).

fof(f91,plain,
    ( spl4_2
  <=> r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f96,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | sK0 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f95,f14])).

fof(f95,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f37])).

fof(f93,plain,
    ( r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f84,f91,f87])).

fof(f84,plain,
    ( r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0))
    | r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_tarski(k2_tarski(sK0,sK1)))
      | r2_hidden(X2,k1_zfmisc_1(sK0))
      | r2_hidden(X2,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f58,f38])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
      | r2_hidden(X0,k1_zfmisc_1(sK1))
      | r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_tarski(k2_tarski(X0,X1)))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f11])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:07:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.38  ipcrm: permission denied for id (789315584)
% 0.15/0.38  ipcrm: permission denied for id (791478274)
% 0.15/0.38  ipcrm: permission denied for id (791511043)
% 0.15/0.39  ipcrm: permission denied for id (791543812)
% 0.15/0.39  ipcrm: permission denied for id (791576581)
% 0.15/0.39  ipcrm: permission denied for id (789348358)
% 0.15/0.39  ipcrm: permission denied for id (789381127)
% 0.15/0.39  ipcrm: permission denied for id (791609352)
% 0.15/0.39  ipcrm: permission denied for id (791642121)
% 0.15/0.39  ipcrm: permission denied for id (794755082)
% 0.15/0.40  ipcrm: permission denied for id (791707659)
% 0.15/0.40  ipcrm: permission denied for id (789446668)
% 0.15/0.40  ipcrm: permission denied for id (794787853)
% 0.15/0.40  ipcrm: permission denied for id (791773198)
% 0.15/0.40  ipcrm: permission denied for id (794820623)
% 0.15/0.40  ipcrm: permission denied for id (791838736)
% 0.15/0.40  ipcrm: permission denied for id (794853393)
% 0.15/0.40  ipcrm: permission denied for id (789577746)
% 0.15/0.41  ipcrm: permission denied for id (789610515)
% 0.15/0.41  ipcrm: permission denied for id (791904276)
% 0.23/0.41  ipcrm: permission denied for id (791937045)
% 0.23/0.41  ipcrm: permission denied for id (794886166)
% 0.23/0.41  ipcrm: permission denied for id (792002583)
% 0.23/0.41  ipcrm: permission denied for id (796229656)
% 0.23/0.41  ipcrm: permission denied for id (792068121)
% 0.23/0.41  ipcrm: permission denied for id (792100890)
% 0.23/0.42  ipcrm: permission denied for id (794951707)
% 0.23/0.42  ipcrm: permission denied for id (796262428)
% 0.23/0.42  ipcrm: permission denied for id (792199197)
% 0.23/0.42  ipcrm: permission denied for id (796295198)
% 0.23/0.42  ipcrm: permission denied for id (792264735)
% 0.23/0.42  ipcrm: permission denied for id (792297504)
% 0.23/0.42  ipcrm: permission denied for id (789807137)
% 0.23/0.42  ipcrm: permission denied for id (789839906)
% 0.23/0.43  ipcrm: permission denied for id (789872675)
% 0.23/0.43  ipcrm: permission denied for id (795050020)
% 0.23/0.43  ipcrm: permission denied for id (792363045)
% 0.23/0.43  ipcrm: permission denied for id (792395814)
% 0.23/0.43  ipcrm: permission denied for id (792428583)
% 0.23/0.43  ipcrm: permission denied for id (795082792)
% 0.23/0.43  ipcrm: permission denied for id (796327977)
% 0.23/0.43  ipcrm: permission denied for id (796360746)
% 0.23/0.44  ipcrm: permission denied for id (792559659)
% 0.23/0.44  ipcrm: permission denied for id (796393516)
% 0.23/0.44  ipcrm: permission denied for id (792625197)
% 0.23/0.44  ipcrm: permission denied for id (795213870)
% 0.23/0.44  ipcrm: permission denied for id (795246639)
% 0.23/0.44  ipcrm: permission denied for id (792756272)
% 0.23/0.44  ipcrm: permission denied for id (792789041)
% 0.23/0.44  ipcrm: permission denied for id (792821810)
% 0.23/0.45  ipcrm: permission denied for id (792854579)
% 0.23/0.45  ipcrm: permission denied for id (795279412)
% 0.23/0.45  ipcrm: permission denied for id (795312181)
% 0.23/0.45  ipcrm: permission denied for id (790036535)
% 0.23/0.45  ipcrm: permission denied for id (792985656)
% 0.23/0.45  ipcrm: permission denied for id (790102073)
% 0.23/0.45  ipcrm: permission denied for id (793018426)
% 0.23/0.46  ipcrm: permission denied for id (790134843)
% 0.23/0.46  ipcrm: permission denied for id (795377724)
% 0.23/0.46  ipcrm: permission denied for id (793083965)
% 0.23/0.46  ipcrm: permission denied for id (793116734)
% 0.23/0.46  ipcrm: permission denied for id (793149503)
% 0.23/0.46  ipcrm: permission denied for id (795410496)
% 0.23/0.46  ipcrm: permission denied for id (793215041)
% 0.23/0.46  ipcrm: permission denied for id (793247810)
% 0.23/0.47  ipcrm: permission denied for id (796459075)
% 0.23/0.47  ipcrm: permission denied for id (795476036)
% 0.23/0.47  ipcrm: permission denied for id (793346117)
% 0.23/0.47  ipcrm: permission denied for id (793378886)
% 0.23/0.47  ipcrm: permission denied for id (795508807)
% 0.23/0.47  ipcrm: permission denied for id (793444424)
% 0.23/0.47  ipcrm: permission denied for id (793477193)
% 0.23/0.47  ipcrm: permission denied for id (790298698)
% 0.23/0.48  ipcrm: permission denied for id (796491851)
% 0.23/0.48  ipcrm: permission denied for id (795574348)
% 0.23/0.48  ipcrm: permission denied for id (790364237)
% 0.23/0.48  ipcrm: permission denied for id (795607118)
% 0.23/0.48  ipcrm: permission denied for id (793641039)
% 0.23/0.48  ipcrm: permission denied for id (795639888)
% 0.23/0.48  ipcrm: permission denied for id (793706577)
% 0.23/0.48  ipcrm: permission denied for id (790495314)
% 0.23/0.49  ipcrm: permission denied for id (790528083)
% 0.23/0.49  ipcrm: permission denied for id (790560852)
% 0.23/0.49  ipcrm: permission denied for id (790626389)
% 0.23/0.49  ipcrm: permission denied for id (793739350)
% 0.23/0.49  ipcrm: permission denied for id (795672663)
% 0.23/0.49  ipcrm: permission denied for id (793804888)
% 0.23/0.49  ipcrm: permission denied for id (790691929)
% 0.23/0.50  ipcrm: permission denied for id (795705434)
% 0.23/0.50  ipcrm: permission denied for id (790757467)
% 0.23/0.50  ipcrm: permission denied for id (793870428)
% 0.23/0.50  ipcrm: permission denied for id (796524637)
% 0.23/0.50  ipcrm: permission denied for id (790888542)
% 0.23/0.50  ipcrm: permission denied for id (790921311)
% 0.23/0.50  ipcrm: permission denied for id (793935968)
% 0.23/0.50  ipcrm: permission denied for id (796557409)
% 0.23/0.51  ipcrm: permission denied for id (790986851)
% 0.23/0.51  ipcrm: permission denied for id (791019620)
% 0.23/0.51  ipcrm: permission denied for id (791052389)
% 0.23/0.51  ipcrm: permission denied for id (796622950)
% 0.23/0.51  ipcrm: permission denied for id (791085159)
% 0.23/0.51  ipcrm: permission denied for id (794067048)
% 0.23/0.51  ipcrm: permission denied for id (796655721)
% 0.23/0.52  ipcrm: permission denied for id (795902058)
% 0.23/0.52  ipcrm: permission denied for id (791150699)
% 0.23/0.52  ipcrm: permission denied for id (794165356)
% 0.23/0.52  ipcrm: permission denied for id (791183469)
% 0.23/0.52  ipcrm: permission denied for id (794198126)
% 0.23/0.52  ipcrm: permission denied for id (795934831)
% 0.23/0.52  ipcrm: permission denied for id (791281777)
% 0.23/0.53  ipcrm: permission denied for id (794296434)
% 0.23/0.53  ipcrm: permission denied for id (796000371)
% 0.23/0.53  ipcrm: permission denied for id (796033140)
% 0.23/0.53  ipcrm: permission denied for id (794394741)
% 0.23/0.53  ipcrm: permission denied for id (796065910)
% 0.23/0.53  ipcrm: permission denied for id (791347319)
% 0.23/0.53  ipcrm: permission denied for id (794460280)
% 0.23/0.53  ipcrm: permission denied for id (794493049)
% 0.23/0.54  ipcrm: permission denied for id (794558587)
% 0.23/0.54  ipcrm: permission denied for id (796131452)
% 0.23/0.54  ipcrm: permission denied for id (794624125)
% 0.23/0.54  ipcrm: permission denied for id (794656894)
% 0.73/0.64  % (374)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.97/0.68  % (364)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.97/0.69  % (377)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.97/0.70  % (388)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.97/0.70  % (363)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.97/0.70  % (373)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.97/0.70  % (373)Refutation found. Thanks to Tanya!
% 0.97/0.70  % SZS status Theorem for theBenchmark
% 0.97/0.70  % SZS output start Proof for theBenchmark
% 0.97/0.70  fof(f256,plain,(
% 0.97/0.70    $false),
% 0.97/0.70    inference(avatar_sat_refutation,[],[f94,f107,f120,f171,f213,f228,f255])).
% 0.97/0.70  fof(f255,plain,(
% 0.97/0.70    ~spl4_4 | ~spl4_8),
% 0.97/0.70    inference(avatar_contradiction_clause,[],[f251])).
% 0.97/0.70  fof(f251,plain,(
% 0.97/0.70    $false | (~spl4_4 | ~spl4_8)),
% 0.97/0.70    inference(unit_resulting_resolution,[],[f10,f241,f16])).
% 0.97/0.70  fof(f16,plain,(
% 0.97/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r3_xboole_0(X0,X1)) )),
% 0.97/0.70    inference(cnf_transformation,[],[f3])).
% 0.97/0.70  fof(f3,axiom,(
% 0.97/0.70    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.97/0.70  fof(f241,plain,(
% 0.97/0.70    r1_tarski(sK0,sK1) | (~spl4_4 | ~spl4_8)),
% 0.97/0.70    inference(superposition,[],[f105,f208])).
% 0.97/0.70  fof(f208,plain,(
% 0.97/0.70    sK1 = k3_tarski(k2_tarski(sK0,sK1)) | ~spl4_8),
% 0.97/0.70    inference(avatar_component_clause,[],[f206])).
% 0.97/0.70  fof(f206,plain,(
% 0.97/0.70    spl4_8 <=> sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.97/0.70  fof(f105,plain,(
% 0.97/0.70    r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) | ~spl4_4),
% 0.97/0.70    inference(avatar_component_clause,[],[f104])).
% 0.97/0.70  fof(f104,plain,(
% 0.97/0.70    spl4_4 <=> r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.97/0.70  fof(f10,plain,(
% 0.97/0.70    ~r3_xboole_0(sK0,sK1)),
% 0.97/0.70    inference(cnf_transformation,[],[f8])).
% 0.97/0.70  fof(f8,plain,(
% 0.97/0.70    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.97/0.70    inference(ennf_transformation,[],[f7])).
% 0.97/0.70  fof(f7,negated_conjecture,(
% 0.97/0.70    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.97/0.70    inference(negated_conjecture,[],[f6])).
% 0.97/0.70  fof(f6,conjecture,(
% 0.97/0.70    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 0.97/0.70  fof(f228,plain,(
% 0.97/0.70    spl4_9),
% 0.97/0.70    inference(avatar_contradiction_clause,[],[f226])).
% 0.97/0.70  fof(f226,plain,(
% 0.97/0.70    $false | spl4_9),
% 0.97/0.70    inference(unit_resulting_resolution,[],[f35,f224,f38])).
% 0.97/0.70  fof(f38,plain,(
% 0.97/0.70    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.97/0.70    inference(equality_resolution,[],[f18])).
% 0.97/0.70  fof(f18,plain,(
% 0.97/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.97/0.70    inference(cnf_transformation,[],[f4])).
% 0.97/0.70  fof(f4,axiom,(
% 0.97/0.70    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.97/0.70  fof(f224,plain,(
% 0.97/0.70    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | spl4_9),
% 0.97/0.70    inference(resolution,[],[f212,f59])).
% 0.97/0.70  fof(f59,plain,(
% 0.97/0.70    ( ! [X0] : (r1_tarski(X0,k3_tarski(k2_tarski(sK0,sK1))) | ~r2_hidden(X0,k1_zfmisc_1(sK1))) )),
% 0.97/0.70    inference(resolution,[],[f49,f37])).
% 0.97/0.70  fof(f37,plain,(
% 0.97/0.70    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.97/0.70    inference(equality_resolution,[],[f19])).
% 0.97/0.70  fof(f19,plain,(
% 0.97/0.70    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.97/0.70    inference(cnf_transformation,[],[f4])).
% 0.97/0.70  fof(f49,plain,(
% 0.97/0.70    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | ~r2_hidden(X1,k1_zfmisc_1(sK1))) )),
% 0.97/0.70    inference(superposition,[],[f39,f28])).
% 0.97/0.70  fof(f28,plain,(
% 0.97/0.70    k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))),
% 0.97/0.70    inference(definition_unfolding,[],[f9,f11,f11])).
% 0.97/0.70  fof(f11,plain,(
% 0.97/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.97/0.70    inference(cnf_transformation,[],[f5])).
% 0.97/0.70  fof(f5,axiom,(
% 0.97/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.97/0.70  fof(f9,plain,(
% 0.97/0.70    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.97/0.70    inference(cnf_transformation,[],[f8])).
% 0.97/0.70  fof(f39,plain,(
% 0.97/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.97/0.70    inference(equality_resolution,[],[f29])).
% 0.97/0.70  fof(f29,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 0.97/0.70    inference(definition_unfolding,[],[f27,f11])).
% 0.97/0.70  fof(f27,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.97/0.70    inference(cnf_transformation,[],[f1])).
% 0.97/0.70  fof(f1,axiom,(
% 0.97/0.70    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.97/0.70  fof(f212,plain,(
% 0.97/0.70    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) | spl4_9),
% 0.97/0.70    inference(avatar_component_clause,[],[f210])).
% 0.97/0.70  fof(f210,plain,(
% 0.97/0.70    spl4_9 <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.97/0.70  fof(f35,plain,(
% 0.97/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.97/0.70    inference(equality_resolution,[],[f13])).
% 0.97/0.70  fof(f13,plain,(
% 0.97/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.97/0.70    inference(cnf_transformation,[],[f2])).
% 0.97/0.70  fof(f2,axiom,(
% 0.97/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.97/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.97/0.70  fof(f213,plain,(
% 0.97/0.70    spl4_8 | ~spl4_9 | ~spl4_1),
% 0.97/0.70    inference(avatar_split_clause,[],[f202,f87,f210,f206])).
% 0.97/0.70  fof(f87,plain,(
% 0.97/0.70    spl4_1 <=> r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.97/0.70  fof(f202,plain,(
% 0.97/0.70    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) | sK1 = k3_tarski(k2_tarski(sK0,sK1)) | ~spl4_1),
% 0.97/0.70    inference(resolution,[],[f201,f14])).
% 0.97/0.70  fof(f14,plain,(
% 0.97/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.97/0.70    inference(cnf_transformation,[],[f2])).
% 0.97/0.70  fof(f201,plain,(
% 0.97/0.70    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1) | ~spl4_1),
% 0.97/0.70    inference(resolution,[],[f89,f37])).
% 0.97/0.70  fof(f89,plain,(
% 0.97/0.70    r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl4_1),
% 0.97/0.70    inference(avatar_component_clause,[],[f87])).
% 0.97/0.70  fof(f171,plain,(
% 0.97/0.70    ~spl4_3),
% 0.97/0.70    inference(avatar_contradiction_clause,[],[f167])).
% 0.97/0.70  fof(f167,plain,(
% 0.97/0.70    $false | ~spl4_3),
% 0.97/0.70    inference(unit_resulting_resolution,[],[f10,f165,f17])).
% 0.97/0.70  fof(f17,plain,(
% 0.97/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r3_xboole_0(X0,X1)) )),
% 0.97/0.70    inference(cnf_transformation,[],[f3])).
% 0.97/0.70  fof(f165,plain,(
% 0.97/0.70    r1_tarski(sK1,sK0) | ~spl4_3),
% 0.97/0.70    inference(resolution,[],[f163,f35])).
% 0.97/0.70  fof(f163,plain,(
% 0.97/0.70    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK0)) ) | ~spl4_3),
% 0.97/0.70    inference(resolution,[],[f127,f38])).
% 0.97/0.70  fof(f127,plain,(
% 0.97/0.70    ( ! [X6] : (~r2_hidden(X6,k1_zfmisc_1(sK1)) | r1_tarski(X6,sK0)) ) | ~spl4_3),
% 0.97/0.70    inference(superposition,[],[f59,f102])).
% 0.97/0.70  fof(f102,plain,(
% 0.97/0.70    sK0 = k3_tarski(k2_tarski(sK0,sK1)) | ~spl4_3),
% 0.97/0.70    inference(avatar_component_clause,[],[f100])).
% 0.97/0.70  fof(f100,plain,(
% 0.97/0.70    spl4_3 <=> sK0 = k3_tarski(k2_tarski(sK0,sK1))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.97/0.70  fof(f120,plain,(
% 0.97/0.70    spl4_4),
% 0.97/0.70    inference(avatar_contradiction_clause,[],[f118])).
% 0.97/0.70  fof(f118,plain,(
% 0.97/0.70    $false | spl4_4),
% 0.97/0.70    inference(unit_resulting_resolution,[],[f35,f116,f38])).
% 0.97/0.70  fof(f116,plain,(
% 0.97/0.70    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl4_4),
% 0.97/0.70    inference(resolution,[],[f106,f50])).
% 0.97/0.70  fof(f50,plain,(
% 0.97/0.70    ( ! [X0] : (r1_tarski(X0,k3_tarski(k2_tarski(sK0,sK1))) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 0.97/0.70    inference(resolution,[],[f48,f37])).
% 0.97/0.70  fof(f48,plain,(
% 0.97/0.70    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 0.97/0.70    inference(superposition,[],[f40,f28])).
% 0.97/0.70  fof(f40,plain,(
% 0.97/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X3,X0)) )),
% 0.97/0.70    inference(equality_resolution,[],[f30])).
% 0.97/0.70  fof(f30,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 0.97/0.70    inference(definition_unfolding,[],[f26,f11])).
% 0.97/0.70  fof(f26,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.97/0.70    inference(cnf_transformation,[],[f1])).
% 0.97/0.70  fof(f106,plain,(
% 0.97/0.70    ~r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) | spl4_4),
% 0.97/0.70    inference(avatar_component_clause,[],[f104])).
% 0.97/0.70  fof(f107,plain,(
% 0.97/0.70    spl4_3 | ~spl4_4 | ~spl4_2),
% 0.97/0.70    inference(avatar_split_clause,[],[f96,f91,f104,f100])).
% 0.97/0.70  fof(f91,plain,(
% 0.97/0.70    spl4_2 <=> r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.97/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.97/0.70  fof(f96,plain,(
% 0.97/0.70    ~r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) | sK0 = k3_tarski(k2_tarski(sK0,sK1)) | ~spl4_2),
% 0.97/0.70    inference(resolution,[],[f95,f14])).
% 0.97/0.70  fof(f95,plain,(
% 0.97/0.70    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK0) | ~spl4_2),
% 0.97/0.70    inference(resolution,[],[f93,f37])).
% 0.97/0.70  fof(f93,plain,(
% 0.97/0.70    r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.97/0.70    inference(avatar_component_clause,[],[f91])).
% 0.97/0.70  fof(f94,plain,(
% 0.97/0.70    spl4_1 | spl4_2),
% 0.97/0.70    inference(avatar_split_clause,[],[f84,f91,f87])).
% 0.97/0.70  fof(f84,plain,(
% 0.97/0.70    r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK0)) | r2_hidden(k3_tarski(k2_tarski(sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.97/0.70    inference(resolution,[],[f81,f35])).
% 0.97/0.70  fof(f81,plain,(
% 0.97/0.70    ( ! [X2] : (~r1_tarski(X2,k3_tarski(k2_tarski(sK0,sK1))) | r2_hidden(X2,k1_zfmisc_1(sK0)) | r2_hidden(X2,k1_zfmisc_1(sK1))) )),
% 0.97/0.70    inference(resolution,[],[f58,f38])).
% 0.97/0.70  fof(f58,plain,(
% 0.97/0.70    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | r2_hidden(X0,k1_zfmisc_1(sK1)) | r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 0.97/0.70    inference(superposition,[],[f41,f28])).
% 0.97/0.70  fof(f41,plain,(
% 0.97/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_tarski(k2_tarski(X0,X1))) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.97/0.70    inference(equality_resolution,[],[f31])).
% 0.97/0.70  fof(f31,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 0.97/0.70    inference(definition_unfolding,[],[f25,f11])).
% 0.97/0.70  fof(f25,plain,(
% 0.97/0.70    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.97/0.70    inference(cnf_transformation,[],[f1])).
% 0.97/0.70  % SZS output end Proof for theBenchmark
% 0.97/0.70  % (373)------------------------------
% 0.97/0.70  % (373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.97/0.70  % (373)Termination reason: Refutation
% 0.97/0.70  
% 0.97/0.70  % (373)Memory used [KB]: 6268
% 0.97/0.70  % (373)Time elapsed: 0.123 s
% 0.97/0.70  % (373)------------------------------
% 0.97/0.70  % (373)------------------------------
% 0.97/0.70  % (370)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.97/0.71  % (32633)Success in time 0.329 s
%------------------------------------------------------------------------------
