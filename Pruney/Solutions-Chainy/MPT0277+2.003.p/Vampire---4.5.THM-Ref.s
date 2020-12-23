%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 147 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 ( 373 expanded)
%              Number of equality atoms :  117 ( 255 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f168,f193,f212,f222,f307,f329])).

fof(f329,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f325,f312])).

fof(f312,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(backward_demodulation,[],[f163,f156])).

fof(f156,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_2
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f163,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f325,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f318,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f318,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_2 ),
    inference(superposition,[],[f141,f156])).

fof(f141,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f307,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f163,f302])).

fof(f302,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(X2,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f256,f93])).

fof(f256,plain,
    ( ! [X13] : r1_tarski(sK0,k2_tarski(X13,sK2))
    | ~ spl5_4 ),
    inference(superposition,[],[f142,f166])).

fof(f166,plain,
    ( sK0 = k2_tarski(sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_4
  <=> sK0 = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f222,plain,
    ( spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f220,f148])).

fof(f148,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f147,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f147,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(inner_rewriting,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f38,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f220,plain,
    ( k1_xboole_0 = sK0
    | spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f219,f157])).

fof(f157,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f219,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f218,f167])).

fof(f167,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f218,plain,
    ( sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f213,f196])).

fof(f196,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f110,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f110,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f54,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f213,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(resolution,[],[f205,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f86,f86])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f205,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f198])).

fof(f198,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f94,f162])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f212,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f210,f153])).

fof(f153,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f210,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f204,f77])).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f204,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_3 ),
    inference(superposition,[],[f136,f162])).

fof(f136,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f101,f102])).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f193,plain,
    ( spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f163,f179])).

fof(f179,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,X10))
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(superposition,[],[f130,f170])).

fof(f170,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f169,f163])).

fof(f169,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f159,f167])).

fof(f159,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f149,f157])).

fof(f149,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f108,f148])).

fof(f108,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f57,f86,f86])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f168,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f109,f165,f161])).

fof(f109,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f55,f86])).

fof(f55,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f158,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f146,f155,f151])).

fof(f146,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(inner_rewriting,[],[f56])).

fof(f56,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:21:26 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.38  ipcrm: permission denied for id (1217822720)
% 0.21/0.38  ipcrm: permission denied for id (1217888258)
% 0.21/0.39  ipcrm: permission denied for id (1217986566)
% 0.21/0.39  ipcrm: permission denied for id (1218019335)
% 0.21/0.39  ipcrm: permission denied for id (1218150413)
% 0.21/0.40  ipcrm: permission denied for id (1218183182)
% 0.21/0.40  ipcrm: permission denied for id (1218248720)
% 0.21/0.40  ipcrm: permission denied for id (1218281489)
% 0.21/0.40  ipcrm: permission denied for id (1218347027)
% 0.21/0.41  ipcrm: permission denied for id (1218445334)
% 0.21/0.41  ipcrm: permission denied for id (1218478103)
% 0.21/0.41  ipcrm: permission denied for id (1218510872)
% 0.21/0.41  ipcrm: permission denied for id (1218576410)
% 0.21/0.41  ipcrm: permission denied for id (1218609179)
% 0.21/0.41  ipcrm: permission denied for id (1218641948)
% 0.21/0.41  ipcrm: permission denied for id (1218674717)
% 0.21/0.42  ipcrm: permission denied for id (1218871331)
% 0.21/0.43  ipcrm: permission denied for id (1218969638)
% 0.21/0.43  ipcrm: permission denied for id (1219067944)
% 0.21/0.43  ipcrm: permission denied for id (1219100713)
% 0.21/0.43  ipcrm: permission denied for id (1219231788)
% 0.21/0.44  ipcrm: permission denied for id (1219264557)
% 0.22/0.44  ipcrm: permission denied for id (1219395633)
% 0.22/0.44  ipcrm: permission denied for id (1219428402)
% 0.22/0.45  ipcrm: permission denied for id (1219690554)
% 0.22/0.45  ipcrm: permission denied for id (1219723323)
% 0.22/0.46  ipcrm: permission denied for id (1219756092)
% 0.22/0.46  ipcrm: permission denied for id (1219887168)
% 0.22/0.46  ipcrm: permission denied for id (1219952705)
% 0.22/0.47  ipcrm: permission denied for id (1220051012)
% 0.22/0.47  ipcrm: permission denied for id (1220116550)
% 0.22/0.47  ipcrm: permission denied for id (1220182088)
% 0.22/0.47  ipcrm: permission denied for id (1220214857)
% 0.22/0.48  ipcrm: permission denied for id (1220313164)
% 0.22/0.48  ipcrm: permission denied for id (1220411471)
% 0.22/0.48  ipcrm: permission denied for id (1220509778)
% 0.22/0.48  ipcrm: permission denied for id (1220542547)
% 0.22/0.49  ipcrm: permission denied for id (1220608085)
% 0.22/0.49  ipcrm: permission denied for id (1220640854)
% 0.22/0.49  ipcrm: permission denied for id (1220771930)
% 0.22/0.49  ipcrm: permission denied for id (1220804699)
% 0.22/0.50  ipcrm: permission denied for id (1220837468)
% 0.22/0.50  ipcrm: permission denied for id (1220903006)
% 0.22/0.50  ipcrm: permission denied for id (1220968544)
% 0.22/0.50  ipcrm: permission denied for id (1221001313)
% 0.22/0.50  ipcrm: permission denied for id (1221066851)
% 0.22/0.51  ipcrm: permission denied for id (1221165158)
% 0.22/0.51  ipcrm: permission denied for id (1221197927)
% 0.22/0.51  ipcrm: permission denied for id (1221230696)
% 0.22/0.51  ipcrm: permission denied for id (1221263465)
% 0.22/0.52  ipcrm: permission denied for id (1221361772)
% 0.22/0.52  ipcrm: permission denied for id (1221394541)
% 0.22/0.52  ipcrm: permission denied for id (1221492849)
% 0.22/0.52  ipcrm: permission denied for id (1221591156)
% 0.22/0.53  ipcrm: permission denied for id (1221623925)
% 0.22/0.53  ipcrm: permission denied for id (1221722232)
% 0.22/0.54  ipcrm: permission denied for id (1221984383)
% 0.39/0.66  % (15938)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.39/0.67  % (15950)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.39/0.67  % (15965)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.39/0.68  % (15965)Refutation found. Thanks to Tanya!
% 0.39/0.68  % SZS status Theorem for theBenchmark
% 0.39/0.68  % SZS output start Proof for theBenchmark
% 0.39/0.68  fof(f332,plain,(
% 0.39/0.68    $false),
% 0.39/0.68    inference(avatar_sat_refutation,[],[f158,f168,f193,f212,f222,f307,f329])).
% 0.39/0.68  fof(f329,plain,(
% 0.39/0.68    ~spl5_2 | spl5_3),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f328])).
% 0.39/0.68  fof(f328,plain,(
% 0.39/0.68    $false | (~spl5_2 | spl5_3)),
% 0.39/0.68    inference(subsumption_resolution,[],[f325,f312])).
% 0.39/0.68  fof(f312,plain,(
% 0.39/0.68    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl5_2 | spl5_3)),
% 0.39/0.68    inference(backward_demodulation,[],[f163,f156])).
% 0.39/0.68  fof(f156,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK2) | ~spl5_2),
% 0.39/0.68    inference(avatar_component_clause,[],[f155])).
% 0.39/0.68  fof(f155,plain,(
% 0.39/0.68    spl5_2 <=> sK0 = k2_tarski(sK1,sK2)),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.39/0.68  fof(f163,plain,(
% 0.39/0.68    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl5_3),
% 0.39/0.68    inference(avatar_component_clause,[],[f161])).
% 0.39/0.68  fof(f161,plain,(
% 0.39/0.68    spl5_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.39/0.68  fof(f325,plain,(
% 0.39/0.68    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl5_2),
% 0.39/0.68    inference(resolution,[],[f318,f93])).
% 0.39/0.68  fof(f93,plain,(
% 0.39/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.39/0.68    inference(cnf_transformation,[],[f8])).
% 0.39/0.68  fof(f8,axiom,(
% 0.39/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.39/0.68  fof(f318,plain,(
% 0.39/0.68    r1_tarski(sK0,sK0) | ~spl5_2),
% 0.39/0.68    inference(superposition,[],[f141,f156])).
% 0.39/0.68  fof(f141,plain,(
% 0.39/0.68    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(equality_resolution,[],[f83])).
% 0.39/0.68  fof(f83,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f45])).
% 0.39/0.68  fof(f45,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.39/0.68    inference(ennf_transformation,[],[f30])).
% 0.39/0.68  fof(f30,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.39/0.68  fof(f307,plain,(
% 0.39/0.68    spl5_3 | ~spl5_4),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f306])).
% 0.39/0.68  fof(f306,plain,(
% 0.39/0.68    $false | (spl5_3 | ~spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f163,f302])).
% 0.39/0.68  fof(f302,plain,(
% 0.39/0.68    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(X2,sK2))) ) | ~spl5_4),
% 0.39/0.68    inference(resolution,[],[f256,f93])).
% 0.39/0.68  fof(f256,plain,(
% 0.39/0.68    ( ! [X13] : (r1_tarski(sK0,k2_tarski(X13,sK2))) ) | ~spl5_4),
% 0.39/0.68    inference(superposition,[],[f142,f166])).
% 0.39/0.68  fof(f166,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK2,sK2) | ~spl5_4),
% 0.39/0.68    inference(avatar_component_clause,[],[f165])).
% 0.39/0.68  fof(f165,plain,(
% 0.39/0.68    spl5_4 <=> sK0 = k2_tarski(sK2,sK2)),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.39/0.68  fof(f142,plain,(
% 0.39/0.68    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(equality_resolution,[],[f127])).
% 0.39/0.68  fof(f127,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k2_tarski(X2,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(definition_unfolding,[],[f82,f86])).
% 0.39/0.68  fof(f86,plain,(
% 0.39/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f27])).
% 0.39/0.68  fof(f27,axiom,(
% 0.39/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.39/0.68  fof(f82,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f45])).
% 0.39/0.68  fof(f222,plain,(
% 0.39/0.68    spl5_2 | ~spl5_3 | spl5_4),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f221])).
% 0.39/0.68  fof(f221,plain,(
% 0.39/0.68    $false | (spl5_2 | ~spl5_3 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f220,f148])).
% 0.39/0.68  fof(f148,plain,(
% 0.39/0.68    k1_xboole_0 != sK0),
% 0.39/0.68    inference(subsumption_resolution,[],[f147,f78])).
% 0.39/0.68  fof(f78,plain,(
% 0.39/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f16])).
% 0.39/0.68  fof(f16,axiom,(
% 0.39/0.68    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.39/0.68  fof(f147,plain,(
% 0.39/0.68    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(inner_rewriting,[],[f53])).
% 0.39/0.68  fof(f53,plain,(
% 0.39/0.68    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(cnf_transformation,[],[f41])).
% 0.39/0.68  fof(f41,plain,(
% 0.39/0.68    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.39/0.68    inference(ennf_transformation,[],[f39])).
% 0.39/0.68  fof(f39,negated_conjecture,(
% 0.39/0.68    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.39/0.68    inference(negated_conjecture,[],[f38])).
% 0.39/0.68  fof(f38,conjecture,(
% 0.39/0.68    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.39/0.68  fof(f220,plain,(
% 0.39/0.68    k1_xboole_0 = sK0 | (spl5_2 | ~spl5_3 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f219,f157])).
% 0.39/0.68  fof(f157,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK1,sK2) | spl5_2),
% 0.39/0.68    inference(avatar_component_clause,[],[f155])).
% 0.39/0.68  fof(f219,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = sK0 | (~spl5_3 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f218,f167])).
% 0.39/0.68  fof(f167,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK2,sK2) | spl5_4),
% 0.39/0.68    inference(avatar_component_clause,[],[f165])).
% 0.39/0.68  fof(f218,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = sK0 | ~spl5_3),
% 0.39/0.68    inference(subsumption_resolution,[],[f213,f196])).
% 0.39/0.68  fof(f196,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK1,sK1) | ~spl5_3),
% 0.39/0.68    inference(subsumption_resolution,[],[f110,f162])).
% 0.39/0.68  fof(f162,plain,(
% 0.39/0.68    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl5_3),
% 0.39/0.68    inference(avatar_component_clause,[],[f161])).
% 0.39/0.68  fof(f110,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK1,sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(definition_unfolding,[],[f54,f86])).
% 0.39/0.68  fof(f54,plain,(
% 0.39/0.68    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(cnf_transformation,[],[f41])).
% 0.39/0.68  fof(f213,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = sK0 | ~spl5_3),
% 0.39/0.68    inference(resolution,[],[f205,f129])).
% 0.39/0.68  fof(f129,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.39/0.68    inference(definition_unfolding,[],[f79,f86,f86])).
% 0.39/0.68  fof(f79,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f45])).
% 0.39/0.68  fof(f205,plain,(
% 0.39/0.68    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl5_3),
% 0.39/0.68    inference(trivial_inequality_removal,[],[f198])).
% 0.39/0.68  fof(f198,plain,(
% 0.39/0.68    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl5_3),
% 0.39/0.68    inference(superposition,[],[f94,f162])).
% 0.39/0.68  fof(f94,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f8])).
% 0.39/0.68  fof(f212,plain,(
% 0.39/0.68    spl5_1 | ~spl5_3),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f211])).
% 0.39/0.68  fof(f211,plain,(
% 0.39/0.68    $false | (spl5_1 | ~spl5_3)),
% 0.39/0.68    inference(subsumption_resolution,[],[f210,f153])).
% 0.39/0.68  fof(f153,plain,(
% 0.39/0.68    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl5_1),
% 0.39/0.68    inference(avatar_component_clause,[],[f151])).
% 0.39/0.68  fof(f151,plain,(
% 0.39/0.68    spl5_1 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.39/0.68  fof(f210,plain,(
% 0.39/0.68    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl5_3),
% 0.39/0.68    inference(forward_demodulation,[],[f204,f77])).
% 0.39/0.68  fof(f77,plain,(
% 0.39/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.39/0.68    inference(cnf_transformation,[],[f11])).
% 0.39/0.68  fof(f11,axiom,(
% 0.39/0.68    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.39/0.68  fof(f204,plain,(
% 0.39/0.68    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | ~spl5_3),
% 0.39/0.68    inference(superposition,[],[f136,f162])).
% 0.39/0.68  fof(f136,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.39/0.68    inference(definition_unfolding,[],[f101,f102])).
% 0.39/0.68  fof(f102,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f15])).
% 0.39/0.68  fof(f15,axiom,(
% 0.39/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.39/0.68  fof(f101,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f14])).
% 0.39/0.68  fof(f14,axiom,(
% 0.39/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.39/0.68  fof(f193,plain,(
% 0.39/0.68    spl5_2 | spl5_3 | spl5_4),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f192])).
% 0.39/0.68  fof(f192,plain,(
% 0.39/0.68    $false | (spl5_2 | spl5_3 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f163,f179])).
% 0.39/0.68  fof(f179,plain,(
% 0.39/0.68    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,X10))) ) | (spl5_2 | spl5_3 | spl5_4)),
% 0.39/0.68    inference(superposition,[],[f130,f170])).
% 0.39/0.68  fof(f170,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK1) | (spl5_2 | spl5_3 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f169,f163])).
% 0.39/0.68  fof(f169,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | (spl5_2 | spl5_4)),
% 0.39/0.68    inference(subsumption_resolution,[],[f159,f167])).
% 0.39/0.68  fof(f159,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl5_2),
% 0.39/0.68    inference(subsumption_resolution,[],[f149,f157])).
% 0.39/0.68  fof(f149,plain,(
% 0.39/0.68    sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(subsumption_resolution,[],[f108,f148])).
% 0.39/0.68  fof(f108,plain,(
% 0.39/0.68    k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(definition_unfolding,[],[f57,f86,f86])).
% 0.39/0.68  fof(f57,plain,(
% 0.39/0.68    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(cnf_transformation,[],[f41])).
% 0.39/0.68  fof(f130,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.39/0.68    inference(definition_unfolding,[],[f85,f86])).
% 0.39/0.68  fof(f85,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f31])).
% 0.39/0.68  fof(f31,axiom,(
% 0.39/0.68    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.39/0.68  fof(f168,plain,(
% 0.39/0.68    ~spl5_3 | ~spl5_4),
% 0.39/0.68    inference(avatar_split_clause,[],[f109,f165,f161])).
% 0.39/0.68  fof(f109,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK2,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(definition_unfolding,[],[f55,f86])).
% 0.39/0.68  fof(f55,plain,(
% 0.39/0.68    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(cnf_transformation,[],[f41])).
% 0.39/0.68  fof(f158,plain,(
% 0.39/0.68    ~spl5_1 | ~spl5_2),
% 0.39/0.68    inference(avatar_split_clause,[],[f146,f155,f151])).
% 0.39/0.68  fof(f146,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 0.39/0.68    inference(inner_rewriting,[],[f56])).
% 0.39/0.68  fof(f56,plain,(
% 0.39/0.68    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.39/0.68    inference(cnf_transformation,[],[f41])).
% 0.39/0.68  % SZS output end Proof for theBenchmark
% 0.39/0.68  % (15965)------------------------------
% 0.39/0.68  % (15965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.68  % (15965)Termination reason: Refutation
% 0.39/0.68  
% 0.39/0.68  % (15965)Memory used [KB]: 6396
% 0.39/0.68  % (15965)Time elapsed: 0.107 s
% 0.39/0.68  % (15965)------------------------------
% 0.39/0.68  % (15965)------------------------------
% 0.39/0.68  % (15957)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.39/0.70  % (15960)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.70  % (15785)Success in time 0.324 s
%------------------------------------------------------------------------------
