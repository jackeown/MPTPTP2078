%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:57 EST 2020

% Result     : Theorem 5.90s
% Output     : Refutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  304 ( 927 expanded)
%              Number of leaves         :   67 ( 368 expanded)
%              Depth                    :   13
%              Number of atoms          :  822 (1905 expanded)
%              Number of equality atoms :  212 ( 785 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f127,f136,f174,f179,f260,f353,f374,f531,f555,f561,f567,f595,f769,f805,f1329,f1382,f1429,f1596,f1614,f1633,f1775,f2106,f2185,f2207,f2416,f2423,f2458,f2561,f2570,f2578,f2715,f2843,f6714,f6715,f6839,f6844,f6845,f6846,f8268,f8298,f8302,f8331,f8335,f8476,f8477,f8481,f8544,f8608,f8684,f8687])).

fof(f8687,plain,
    ( ~ spl12_126
    | spl12_49
    | ~ spl12_122 ),
    inference(avatar_split_clause,[],[f8557,f8265,f1772,f8680])).

fof(f8680,plain,
    ( spl12_126
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_126])])).

fof(f1772,plain,
    ( spl12_49
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).

fof(f8265,plain,
    ( spl12_122
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_122])])).

fof(f8557,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl12_49
    | ~ spl12_122 ),
    inference(forward_demodulation,[],[f8556,f111])).

fof(f111,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f8556,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | spl12_49
    | ~ spl12_122 ),
    inference(forward_demodulation,[],[f1774,f8267])).

fof(f8267,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl12_122 ),
    inference(avatar_component_clause,[],[f8265])).

fof(f1774,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0)
    | spl12_49 ),
    inference(avatar_component_clause,[],[f1772])).

fof(f8684,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8608,plain,
    ( ~ spl12_46
    | ~ spl12_47 ),
    inference(avatar_contradiction_clause,[],[f8603])).

fof(f8603,plain,
    ( $false
    | ~ spl12_46
    | ~ spl12_47 ),
    inference(unit_resulting_resolution,[],[f1613,f104,f1629,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f1629,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f1627])).

fof(f1627,plain,
    ( spl12_47
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1613,plain,
    ( ! [X6] : ~ r2_hidden(X6,k2_relat_1(sK2))
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1612,plain,
    ( spl12_46
  <=> ! [X6] : ~ r2_hidden(X6,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f8544,plain,
    ( spl12_9
    | ~ spl12_72
    | ~ spl12_122 ),
    inference(avatar_split_clause,[],[f8491,f8265,f2840,f257])).

fof(f257,plain,
    ( spl12_9
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f2840,plain,
    ( spl12_72
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).

fof(f8491,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl12_72
    | ~ spl12_122 ),
    inference(forward_demodulation,[],[f8490,f111])).

fof(f8490,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK2))
    | ~ spl12_72
    | ~ spl12_122 ),
    inference(forward_demodulation,[],[f2842,f8267])).

fof(f2842,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2))
    | ~ spl12_72 ),
    inference(avatar_component_clause,[],[f2840])).

fof(f8481,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 != k1_setfam_1(sK2)
    | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK2,sK2)),k2_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8477,plain,
    ( sK0 != k1_setfam_1(sK2)
    | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | r1_tarski(k1_relat_1(k2_zfmisc_1(sK2,sK2)),k2_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8476,plain,
    ( ~ spl12_62
    | ~ spl12_27
    | spl12_64 ),
    inference(avatar_split_clause,[],[f6898,f2358,f661,f2317])).

fof(f2317,plain,
    ( spl12_62
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f661,plain,
    ( spl12_27
  <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f2358,plain,
    ( spl12_64
  <=> r1_tarski(k1_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f6898,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl12_27
    | spl12_64 ),
    inference(resolution,[],[f2360,f1721])).

fof(f1721,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(sK2),X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl12_27 ),
    inference(duplicate_literal_removal,[],[f1720])).

fof(f1720,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(k1_relat_1(sK2),X1)
        | r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl12_27 ),
    inference(superposition,[],[f44,f1564])).

fof(f1564,plain,
    ( ! [X6] :
        ( sK0 = sK3(k1_relat_1(sK2),X6)
        | r1_tarski(k1_relat_1(sK2),X6) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1554,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1554,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK0 = X3 )
    | ~ spl12_27 ),
    inference(resolution,[],[f1543,f108])).

fof(f108,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1543,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl12_27 ),
    inference(superposition,[],[f103,f663])).

fof(f663,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f661])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f73,f79,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2360,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK2)
    | spl12_64 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f8335,plain,
    ( sK2 != k2_relat_1(k1_xboole_0)
    | sK0 != k1_setfam_1(sK2)
    | sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8331,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | sK2 != k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK2,k1_xboole_0)
    | r1_tarski(sK2,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8302,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8298,plain,
    ( spl12_122
    | spl12_4
    | ~ spl12_121 ),
    inference(avatar_split_clause,[],[f8273,f8261,f133,f8265])).

fof(f133,plain,
    ( spl12_4
  <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f8261,plain,
    ( spl12_121
  <=> sK0 = sK10(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_121])])).

fof(f8273,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | spl12_4
    | ~ spl12_121 ),
    inference(trivial_inequality_removal,[],[f8270])).

fof(f8270,plain,
    ( sK0 != sK0
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | spl12_4
    | ~ spl12_121 ),
    inference(superposition,[],[f2151,f8263])).

fof(f8263,plain,
    ( sK0 = sK10(k1_relat_1(sK2),sK0)
    | ~ spl12_121 ),
    inference(avatar_component_clause,[],[f8261])).

fof(f2151,plain,
    ( ! [X1] :
        ( sK0 != sK10(X1,sK0)
        | k1_xboole_0 = X1
        | k1_relat_1(sK2) != X1 )
    | spl12_4 ),
    inference(superposition,[],[f135,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | sK10(X0,X1) != X1 ) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK10(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f135,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl12_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f8268,plain,
    ( spl12_121
    | spl12_122
    | spl12_4
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f2263,f661,f133,f8265,f8261])).

fof(f2263,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | sK0 = sK10(k1_relat_1(sK2),sK0)
    | spl12_4
    | ~ spl12_27 ),
    inference(trivial_inequality_removal,[],[f2255])).

fof(f2255,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 = sK10(k1_relat_1(sK2),sK0)
    | spl12_4
    | ~ spl12_27 ),
    inference(resolution,[],[f2150,f1554])).

fof(f2150,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(X0,sK0),X0)
        | k1_xboole_0 = X0
        | k1_relat_1(sK2) != X0 )
    | spl12_4 ),
    inference(superposition,[],[f135,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6846,plain,
    ( sK2 != k2_relat_1(k1_xboole_0)
    | sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | r1_tarski(sK2,k1_relat_1(sK2))
    | ~ r1_tarski(sK2,k2_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6845,plain,
    ( ~ spl12_67
    | ~ spl12_58
    | spl12_66 ),
    inference(avatar_split_clause,[],[f6827,f2567,f2099,f2575])).

fof(f2575,plain,
    ( spl12_67
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_67])])).

fof(f2099,plain,
    ( spl12_58
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f2567,plain,
    ( spl12_66
  <=> sK2 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_66])])).

fof(f6827,plain,
    ( k1_xboole_0 != sK2
    | ~ spl12_58
    | spl12_66 ),
    inference(backward_demodulation,[],[f2568,f2101])).

fof(f2101,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f2099])).

fof(f2568,plain,
    ( sK2 != k2_relat_1(sK2)
    | spl12_66 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f6844,plain,
    ( ~ spl12_9
    | ~ spl12_50
    | spl12_67 ),
    inference(avatar_contradiction_clause,[],[f6841])).

fof(f6841,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_50
    | spl12_67 ),
    inference(unit_resulting_resolution,[],[f2577,f258,f1858,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1858,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f1857,plain,
    ( spl12_50
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f258,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f2577,plain,
    ( k1_xboole_0 != sK2
    | spl12_67 ),
    inference(avatar_component_clause,[],[f2575])).

fof(f6839,plain,
    ( spl12_50
    | ~ spl12_38
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f6836,f2099,f1320,f1857])).

fof(f1320,plain,
    ( spl12_38
  <=> r1_tarski(k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f6836,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl12_38
    | ~ spl12_58 ),
    inference(forward_demodulation,[],[f1321,f2101])).

fof(f1321,plain,
    ( r1_tarski(k2_relat_1(sK2),sK2)
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f6715,plain,
    ( sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | sK2 != k2_relat_1(sK2)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6714,plain,
    ( sK0 != k1_setfam_1(sK2)
    | sK1 != k1_setfam_1(sK2)
    | k4_tarski(sK0,sK1) != k1_setfam_1(sK2)
    | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | sK2 != k2_relat_1(sK2)
    | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2843,plain,
    ( ~ spl12_1
    | spl12_72
    | ~ spl12_66 ),
    inference(avatar_split_clause,[],[f2573,f2567,f2840,f119])).

fof(f119,plain,
    ( spl12_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f2573,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl12_66 ),
    inference(superposition,[],[f35,f2569])).

fof(f2569,plain,
    ( sK2 = k2_relat_1(sK2)
    | ~ spl12_66 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f2715,plain,
    ( ~ spl12_69
    | ~ spl12_12
    | ~ spl12_45 ),
    inference(avatar_split_clause,[],[f2706,f1608,f351,f2712])).

fof(f2712,plain,
    ( spl12_69
  <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).

fof(f351,plain,
    ( spl12_12
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f1608,plain,
    ( spl12_45
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).

fof(f2706,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl12_12
    | ~ spl12_45 ),
    inference(resolution,[],[f2446,f1610])).

fof(f1610,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl12_45 ),
    inference(avatar_component_clause,[],[f1608])).

fof(f2446,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl12_12 ),
    inference(resolution,[],[f352,f42])).

fof(f352,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f351])).

fof(f2578,plain,
    ( ~ spl12_67
    | spl12_58
    | ~ spl12_66 ),
    inference(avatar_split_clause,[],[f2571,f2567,f2099,f2575])).

fof(f2571,plain,
    ( k1_xboole_0 != sK2
    | spl12_58
    | ~ spl12_66 ),
    inference(superposition,[],[f2100,f2569])).

fof(f2100,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl12_58 ),
    inference(avatar_component_clause,[],[f2099])).

fof(f2570,plain,
    ( spl12_66
    | ~ spl12_3
    | ~ spl12_6
    | ~ spl12_29 ),
    inference(avatar_split_clause,[],[f2551,f763,f176,f129,f2567])).

fof(f129,plain,
    ( spl12_3
  <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f176,plain,
    ( spl12_6
  <=> sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f763,plain,
    ( spl12_29
  <=> sK1 = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f2551,plain,
    ( sK2 = k2_relat_1(sK2)
    | ~ spl12_3
    | ~ spl12_6
    | ~ spl12_29 ),
    inference(backward_demodulation,[],[f130,f2509])).

fof(f2509,plain,
    ( sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl12_6
    | ~ spl12_29 ),
    inference(backward_demodulation,[],[f178,f765])).

fof(f765,plain,
    ( sK1 = k1_setfam_1(sK2)
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f763])).

fof(f178,plain,
    ( sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f130,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f2561,plain,
    ( ~ spl12_31
    | ~ spl12_27
    | spl12_38 ),
    inference(avatar_split_clause,[],[f1737,f1320,f661,f802])).

fof(f802,plain,
    ( spl12_31
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f1737,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl12_27
    | spl12_38 ),
    inference(resolution,[],[f1735,f1322])).

fof(f1322,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK2)
    | spl12_38 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f1735,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(sK2),X1)
        | ~ r2_hidden(sK1,X1) )
    | ~ spl12_27 ),
    inference(duplicate_literal_removal,[],[f1734])).

fof(f1734,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | r1_tarski(k2_relat_1(sK2),X1)
        | r1_tarski(k2_relat_1(sK2),X1) )
    | ~ spl12_27 ),
    inference(superposition,[],[f44,f1580])).

fof(f1580,plain,
    ( ! [X6] :
        ( sK1 = sK3(k2_relat_1(sK2),X6)
        | r1_tarski(k2_relat_1(sK2),X6) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1568,f43])).

fof(f1568,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | sK1 = X1 )
    | ~ spl12_27 ),
    inference(resolution,[],[f1544,f106])).

fof(f106,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1544,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | sK1 = X3 )
    | ~ spl12_27 ),
    inference(superposition,[],[f102,f663])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f74,f79,f79])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2458,plain,
    ( ~ spl12_12
    | ~ spl12_61 ),
    inference(avatar_contradiction_clause,[],[f2454])).

fof(f2454,plain,
    ( $false
    | ~ spl12_12
    | ~ spl12_61 ),
    inference(resolution,[],[f352,f2184])).

fof(f2184,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl12_61 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2182,plain,
    ( spl12_61
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).

fof(f2423,plain,
    ( ~ spl12_1
    | spl12_9
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f2422,f2099,f257,f119])).

fof(f2422,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl12_58 ),
    inference(forward_demodulation,[],[f2421,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2421,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | ~ spl12_58 ),
    inference(superposition,[],[f35,f2101])).

fof(f2416,plain,
    ( spl12_58
    | spl12_3
    | ~ spl12_59 ),
    inference(avatar_split_clause,[],[f2397,f2103,f129,f2099])).

fof(f2103,plain,
    ( spl12_59
  <=> sK1 = sK10(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f2397,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | spl12_3
    | ~ spl12_59 ),
    inference(trivial_inequality_removal,[],[f2396])).

fof(f2396,plain,
    ( sK1 != sK1
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | spl12_3
    | ~ spl12_59 ),
    inference(superposition,[],[f2213,f2105])).

fof(f2105,plain,
    ( sK1 = sK10(k2_relat_1(sK2),sK1)
    | ~ spl12_59 ),
    inference(avatar_component_clause,[],[f2103])).

fof(f2213,plain,
    ( ! [X1] :
        ( sK1 != sK10(X1,sK1)
        | k1_xboole_0 = X1
        | k2_relat_1(sK2) != X1 )
    | spl12_3 ),
    inference(superposition,[],[f131,f85])).

fof(f131,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f2207,plain,
    ( ~ spl12_5
    | ~ spl12_20
    | ~ spl12_48 ),
    inference(avatar_contradiction_clause,[],[f2192])).

fof(f2192,plain,
    ( $false
    | ~ spl12_5
    | ~ spl12_20
    | ~ spl12_48 ),
    inference(unit_resulting_resolution,[],[f594,f1632,f189])).

fof(f189,plain,
    ( ! [X13] :
        ( r2_hidden(sK0,k1_relat_1(X13))
        | ~ r2_hidden(k1_setfam_1(sK2),X13) )
    | ~ spl12_5 ),
    inference(superposition,[],[f109,f173])).

fof(f173,plain,
    ( k4_tarski(sK0,sK1) = k1_setfam_1(sK2)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl12_5
  <=> k4_tarski(sK0,sK1) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f109,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1632,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_relat_1(sK2))
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f1631,plain,
    ( spl12_48
  <=> ! [X7] : ~ r2_hidden(X7,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f594,plain,
    ( r2_hidden(k1_setfam_1(sK2),sK2)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl12_20
  <=> r2_hidden(k1_setfam_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f2185,plain,
    ( spl12_61
    | ~ spl12_47
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f2170,f2099,f1627,f2182])).

fof(f2170,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl12_47
    | ~ spl12_58 ),
    inference(backward_demodulation,[],[f1629,f2101])).

fof(f2106,plain,
    ( spl12_58
    | spl12_59
    | spl12_3
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f1583,f661,f129,f2103,f2099])).

fof(f1583,plain,
    ( sK1 = sK10(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = k2_relat_1(sK2)
    | spl12_3
    | ~ spl12_27 ),
    inference(trivial_inequality_removal,[],[f1581])).

fof(f1581,plain,
    ( sK1 = sK10(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | spl12_3
    | ~ spl12_27 ),
    inference(resolution,[],[f1568,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(X0,sK1),X0)
        | k1_xboole_0 = X0
        | k2_relat_1(sK2) != X0 )
    | spl12_3 ),
    inference(superposition,[],[f131,f86])).

fof(f1775,plain,
    ( ~ spl12_1
    | ~ spl12_49
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f1479,f767,f176,f1772,f119])).

fof(f767,plain,
    ( spl12_30
  <=> ! [X0] : ~ r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f1479,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(resolution,[],[f1455,f35])).

fof(f1455,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(resolution,[],[f927,f826])).

fof(f826,plain,
    ( ! [X28] :
        ( r2_hidden(k1_setfam_1(sK2),X28)
        | ~ r1_tarski(sK2,X28) )
    | ~ spl12_6 ),
    inference(superposition,[],[f96,f178])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f927,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_setfam_1(sK2),X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl12_30 ),
    inference(superposition,[],[f847,f111])).

fof(f847,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(X1,sK2))
        | ~ r2_hidden(k1_setfam_1(sK2),X0) )
    | ~ spl12_30 ),
    inference(resolution,[],[f768,f42])).

fof(f768,plain,
    ( ! [X0] : ~ r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2))
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f767])).

fof(f1633,plain,
    ( spl12_47
    | spl12_48
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f1624,f661,f1631,f1627])).

fof(f1624,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k1_relat_1(sK2))
        | r2_hidden(sK1,k2_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1587,f107])).

fof(f107,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1587,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(duplicate_literal_removal,[],[f1586])).

fof(f1586,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(superposition,[],[f108,f1570])).

fof(f1570,plain,
    ( ! [X3] :
        ( sK1 = sK8(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1544,f108])).

fof(f1614,plain,
    ( spl12_45
    | spl12_46
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f1604,f661,f1612,f1608])).

fof(f1604,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_relat_1(sK2))
        | r2_hidden(sK0,k1_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1585,f109])).

fof(f1585,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(duplicate_literal_removal,[],[f1584])).

fof(f1584,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(superposition,[],[f106,f1552])).

fof(f1552,plain,
    ( ! [X1] :
        ( sK0 = sK5(sK2,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl12_27 ),
    inference(resolution,[],[f1543,f106])).

fof(f1596,plain,
    ( ~ spl12_43
    | spl12_44
    | ~ spl12_6
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f1562,f661,f176,f1593,f1589])).

fof(f1589,plain,
    ( spl12_43
  <=> r1_tarski(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f1593,plain,
    ( spl12_44
  <=> sK0 = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f1562,plain,
    ( sK0 = k1_setfam_1(sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK2))
    | ~ spl12_6
    | ~ spl12_27 ),
    inference(resolution,[],[f1554,f826])).

fof(f1429,plain,
    ( ~ spl12_8
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f848,f767,f250])).

fof(f250,plain,
    ( spl12_8
  <=> r2_hidden(k1_setfam_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f848,plain,
    ( ~ r2_hidden(k1_setfam_1(sK2),k1_xboole_0)
    | ~ spl12_30 ),
    inference(superposition,[],[f768,f111])).

fof(f1382,plain,
    ( ~ spl12_6
    | spl12_17
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f1365])).

fof(f1365,plain,
    ( $false
    | ~ spl12_6
    | spl12_17
    | ~ spl12_20 ),
    inference(unit_resulting_resolution,[],[f530,f594,f1362])).

fof(f1362,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_setfam_1(sK2),X1)
        | r1_tarski(k2_relat_1(k1_xboole_0),X1) )
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_setfam_1(sK2),X1)
        | r1_tarski(k2_relat_1(k1_xboole_0),X1)
        | r1_tarski(k2_relat_1(k1_xboole_0),X1) )
    | ~ spl12_6 ),
    inference(superposition,[],[f44,f297])).

fof(f297,plain,
    ( ! [X6] :
        ( k1_setfam_1(sK2) = sK3(k2_relat_1(k1_xboole_0),X6)
        | r1_tarski(k2_relat_1(k1_xboole_0),X6) )
    | ~ spl12_6 ),
    inference(resolution,[],[f285,f43])).

fof(f285,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0))
        | k1_setfam_1(sK2) = X1 )
    | ~ spl12_6 ),
    inference(resolution,[],[f283,f106])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | k1_setfam_1(sK2) = X1 )
    | ~ spl12_6 ),
    inference(superposition,[],[f204,f111])).

fof(f204,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(X4,sK2))
        | k1_setfam_1(sK2) = X3 )
    | ~ spl12_6 ),
    inference(superposition,[],[f99,f178])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f530,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK2)
    | spl12_17 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl12_17
  <=> r1_tarski(k2_relat_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f1329,plain,
    ( spl12_27
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f146,f124,f661])).

fof(f124,plain,
    ( spl12_2
  <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f146,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl12_2 ),
    inference(superposition,[],[f88,f126])).

fof(f126,plain,
    ( sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f59,f79,f76,f76])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f805,plain,
    ( spl12_31
    | ~ spl12_20
    | ~ spl12_29 ),
    inference(avatar_split_clause,[],[f795,f763,f592,f802])).

fof(f795,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl12_20
    | ~ spl12_29 ),
    inference(backward_demodulation,[],[f594,f765])).

fof(f769,plain,
    ( spl12_29
    | spl12_30
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f282,f176,f171,f767,f763])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2))
        | sK1 = k1_setfam_1(sK2) )
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(superposition,[],[f204,f173])).

fof(f595,plain,
    ( spl12_20
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f582,f176,f592])).

fof(f582,plain,
    ( r2_hidden(k1_setfam_1(sK2),sK2)
    | ~ spl12_6 ),
    inference(resolution,[],[f211,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f211,plain,
    ( ! [X22] : r2_hidden(k4_tarski(k1_setfam_1(sK2),X22),k2_zfmisc_1(sK2,k2_enumset1(X22,X22,X22,X22)))
    | ~ spl12_6 ),
    inference(superposition,[],[f117,f178])).

fof(f117,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X3,X1] :
      ( X1 != X3
      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f75,f79,f79])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f567,plain,
    ( spl12_19
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f565,f176,f558])).

fof(f558,plain,
    ( spl12_19
  <=> r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f565,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f563])).

fof(f563,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl12_6 ),
    inference(resolution,[],[f337,f43])).

fof(f337,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(X3,k1_relat_1(k1_xboole_0)),k1_xboole_0)
        | r1_tarski(X3,k1_relat_1(k1_xboole_0)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f332,f44])).

fof(f332,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl12_6 ),
    inference(superposition,[],[f321,f111])).

fof(f321,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,k1_relat_1(k2_zfmisc_1(X7,sK2)))
        | ~ r2_hidden(X6,X7) )
    | ~ spl12_6 ),
    inference(resolution,[],[f210,f109])).

fof(f210,plain,
    ( ! [X21,X20] :
        ( r2_hidden(k4_tarski(X20,k1_setfam_1(sK2)),k2_zfmisc_1(X21,sK2))
        | ~ r2_hidden(X20,X21) )
    | ~ spl12_6 ),
    inference(superposition,[],[f115,f178])).

fof(f115,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f561,plain,
    ( spl12_15
    | ~ spl12_19
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f556,f552,f558,f496])).

fof(f496,plain,
    ( spl12_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f552,plain,
    ( spl12_18
  <=> r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f556,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl12_18 ),
    inference(resolution,[],[f554,f41])).

fof(f554,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f552])).

fof(f555,plain,
    ( spl12_18
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f550,f124,f552])).

fof(f550,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl12_2 ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl12_2 ),
    inference(resolution,[],[f243,f44])).

fof(f243,plain,
    ( ! [X6] :
        ( r2_hidden(sK3(k1_relat_1(k1_xboole_0),X6),k1_xboole_0)
        | r1_tarski(k1_relat_1(k1_xboole_0),X6) )
    | ~ spl12_2 ),
    inference(resolution,[],[f233,f43])).

fof(f233,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f229,f108])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl12_2 ),
    inference(superposition,[],[f151,f111])).

fof(f151,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,sK2))
        | r2_hidden(X5,X7) )
    | ~ spl12_2 ),
    inference(superposition,[],[f100,f126])).

fof(f531,plain,
    ( spl12_16
    | ~ spl12_17
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f502,f371,f528,f524])).

fof(f524,plain,
    ( spl12_16
  <=> sK2 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f371,plain,
    ( spl12_14
  <=> r1_tarski(sK2,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f502,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK2)
    | sK2 = k2_relat_1(k1_xboole_0)
    | ~ spl12_14 ),
    inference(resolution,[],[f373,f41])).

fof(f373,plain,
    ( r1_tarski(sK2,k2_relat_1(k1_xboole_0))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f371])).

fof(f374,plain,
    ( spl12_14
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f356,f347,f171,f124,f371])).

fof(f347,plain,
    ( spl12_11
  <=> r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f356,plain,
    ( r1_tarski(sK2,k2_relat_1(k1_xboole_0))
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_11 ),
    inference(resolution,[],[f349,f194])).

fof(f194,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k1_setfam_1(sK2),X27)
        | r1_tarski(sK2,X27) )
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f168,f173])).

fof(f168,plain,
    ( ! [X27] :
        ( r1_tarski(sK2,X27)
        | ~ r2_hidden(k4_tarski(sK0,sK1),X27) )
    | ~ spl12_2 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ! [X27] :
        ( r1_tarski(sK2,X27)
        | ~ r2_hidden(k4_tarski(sK0,sK1),X27)
        | ~ r2_hidden(k4_tarski(sK0,sK1),X27) )
    | ~ spl12_2 ),
    inference(superposition,[],[f95,f126])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f349,plain,
    ( r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f347])).

fof(f353,plain,
    ( spl12_11
    | spl12_12
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f345,f176,f351,f347])).

fof(f345,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f323,f107])).

fof(f323,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_setfam_1(sK2)),k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl12_6 ),
    inference(superposition,[],[f210,f111])).

fof(f260,plain,
    ( ~ spl12_9
    | ~ spl12_2
    | ~ spl12_5
    | spl12_8 ),
    inference(avatar_split_clause,[],[f254,f250,f171,f124,f257])).

fof(f254,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl12_2
    | ~ spl12_5
    | spl12_8 ),
    inference(resolution,[],[f252,f192])).

fof(f192,plain,
    ( ! [X28] :
        ( r2_hidden(k1_setfam_1(sK2),X28)
        | ~ r1_tarski(sK2,X28) )
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f163,f173])).

fof(f163,plain,
    ( ! [X28] :
        ( ~ r1_tarski(sK2,X28)
        | r2_hidden(k4_tarski(sK0,sK1),X28) )
    | ~ spl12_2 ),
    inference(superposition,[],[f96,f126])).

fof(f252,plain,
    ( ~ r2_hidden(k1_setfam_1(sK2),k1_xboole_0)
    | spl12_8 ),
    inference(avatar_component_clause,[],[f250])).

fof(f179,plain,
    ( spl12_6
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f169,f124,f176])).

fof(f169,plain,
    ( sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f126,f147])).

fof(f147,plain,
    ( k4_tarski(sK0,sK1) = k1_setfam_1(sK2)
    | ~ spl12_2 ),
    inference(superposition,[],[f83,f126])).

fof(f83,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f79])).

fof(f32,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f174,plain,
    ( spl12_5
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f147,f124,f171])).

fof(f136,plain,
    ( ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f81,f133,f129])).

fof(f81,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f28,f79,f79])).

fof(f28,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k1_tarski(sK1) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f127,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f80,f124])).

fof(f80,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f79])).

fof(f30,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f122,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f29,f119])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (23024)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (23038)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (23031)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.66/0.58  % (23035)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.66/0.59  % (23043)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.66/0.59  % (23051)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.66/0.60  % (23044)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.66/0.61  % (23036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.66/0.61  % (23047)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.61  % (23023)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.61  % (23028)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.62  % (23022)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.66/0.62  % (23025)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.66/0.62  % (23021)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.66/0.63  % (23049)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.66/0.63  % (23037)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.66/0.63  % (23046)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.66/0.63  % (23042)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.66/0.63  % (23033)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.64  % (23050)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.66/0.64  % (23045)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.66/0.64  % (23039)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.66/0.64  % (23034)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.66/0.64  % (23030)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.66/0.64  % (23032)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.66/0.65  % (23026)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.66/0.66  % (23027)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.30/0.67  % (23029)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.30/0.68  % (23048)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.47/0.69  % (23040)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 3.47/0.85  % (23026)Time limit reached!
% 3.47/0.85  % (23026)------------------------------
% 3.47/0.85  % (23026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.86  % (23026)Termination reason: Time limit
% 3.47/0.86  
% 3.47/0.86  % (23026)Memory used [KB]: 7675
% 3.47/0.86  % (23026)Time elapsed: 0.425 s
% 3.47/0.86  % (23026)------------------------------
% 3.47/0.86  % (23026)------------------------------
% 3.93/0.93  % (23031)Time limit reached!
% 3.93/0.93  % (23031)------------------------------
% 3.93/0.93  % (23031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.93  % (23033)Time limit reached!
% 3.93/0.93  % (23033)------------------------------
% 3.93/0.93  % (23033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.93  % (23033)Termination reason: Time limit
% 3.93/0.93  
% 3.93/0.93  % (23033)Memory used [KB]: 8059
% 3.93/0.93  % (23033)Time elapsed: 0.505 s
% 3.93/0.93  % (23033)------------------------------
% 3.93/0.93  % (23033)------------------------------
% 3.93/0.93  % (23031)Termination reason: Time limit
% 3.93/0.93  
% 3.93/0.93  % (23031)Memory used [KB]: 15095
% 3.93/0.93  % (23031)Time elapsed: 0.509 s
% 3.93/0.93  % (23031)------------------------------
% 3.93/0.93  % (23031)------------------------------
% 3.93/0.93  % (23038)Time limit reached!
% 3.93/0.93  % (23038)------------------------------
% 3.93/0.93  % (23038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.93  % (23038)Termination reason: Time limit
% 3.93/0.93  % (23038)Termination phase: Saturation
% 3.93/0.93  
% 3.93/0.93  % (23038)Memory used [KB]: 14583
% 3.93/0.93  % (23038)Time elapsed: 0.500 s
% 3.93/0.93  % (23038)------------------------------
% 3.93/0.93  % (23038)------------------------------
% 3.93/0.95  % (23022)Time limit reached!
% 3.93/0.95  % (23022)------------------------------
% 3.93/0.95  % (23022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/0.97  % (23022)Termination reason: Time limit
% 4.59/0.97  
% 4.59/0.97  % (23022)Memory used [KB]: 7547
% 4.59/0.97  % (23022)Time elapsed: 0.520 s
% 4.59/0.97  % (23022)------------------------------
% 4.59/0.97  % (23022)------------------------------
% 4.59/0.97  % (23021)Time limit reached!
% 4.59/0.97  % (23021)------------------------------
% 4.59/0.97  % (23021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/0.97  % (23021)Termination reason: Time limit
% 4.59/0.97  % (23021)Termination phase: Saturation
% 4.59/0.97  
% 4.59/0.97  % (23021)Memory used [KB]: 4221
% 4.59/0.97  % (23021)Time elapsed: 0.500 s
% 4.59/0.97  % (23021)------------------------------
% 4.59/0.97  % (23021)------------------------------
% 4.81/0.99  % (23060)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 5.05/1.04  % (23050)Time limit reached!
% 5.05/1.04  % (23050)------------------------------
% 5.05/1.04  % (23050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.04  % (23037)Time limit reached!
% 5.05/1.04  % (23037)------------------------------
% 5.05/1.04  % (23037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.04  % (23037)Termination reason: Time limit
% 5.05/1.04  
% 5.05/1.04  % (23037)Memory used [KB]: 14967
% 5.05/1.04  % (23037)Time elapsed: 0.611 s
% 5.05/1.04  % (23037)------------------------------
% 5.05/1.04  % (23037)------------------------------
% 5.05/1.04  % (23050)Termination reason: Time limit
% 5.05/1.04  
% 5.05/1.04  % (23050)Memory used [KB]: 7803
% 5.05/1.04  % (23050)Time elapsed: 0.605 s
% 5.05/1.04  % (23050)------------------------------
% 5.05/1.04  % (23050)------------------------------
% 5.17/1.05  % (23069)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.17/1.06  % (23068)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.17/1.06  % (23090)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.17/1.07  % (23072)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.17/1.10  % (23087)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.17/1.10  % (23028)Time limit reached!
% 5.17/1.10  % (23028)------------------------------
% 5.17/1.10  % (23028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.12  % (23028)Termination reason: Time limit
% 5.17/1.12  
% 5.17/1.12  % (23028)Memory used [KB]: 11897
% 5.17/1.12  % (23028)Time elapsed: 0.609 s
% 5.17/1.12  % (23028)------------------------------
% 5.17/1.12  % (23028)------------------------------
% 5.90/1.14  % (23044)Refutation found. Thanks to Tanya!
% 5.90/1.14  % SZS status Theorem for theBenchmark
% 5.90/1.14  % (23122)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.90/1.16  % SZS output start Proof for theBenchmark
% 5.90/1.16  fof(f8688,plain,(
% 5.90/1.16    $false),
% 5.90/1.16    inference(avatar_sat_refutation,[],[f122,f127,f136,f174,f179,f260,f353,f374,f531,f555,f561,f567,f595,f769,f805,f1329,f1382,f1429,f1596,f1614,f1633,f1775,f2106,f2185,f2207,f2416,f2423,f2458,f2561,f2570,f2578,f2715,f2843,f6714,f6715,f6839,f6844,f6845,f6846,f8268,f8298,f8302,f8331,f8335,f8476,f8477,f8481,f8544,f8608,f8684,f8687])).
% 5.90/1.16  fof(f8687,plain,(
% 5.90/1.16    ~spl12_126 | spl12_49 | ~spl12_122),
% 5.90/1.16    inference(avatar_split_clause,[],[f8557,f8265,f1772,f8680])).
% 5.90/1.16  fof(f8680,plain,(
% 5.90/1.16    spl12_126 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_126])])).
% 5.90/1.16  fof(f1772,plain,(
% 5.90/1.16    spl12_49 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).
% 5.90/1.16  fof(f8265,plain,(
% 5.90/1.16    spl12_122 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_122])])).
% 5.90/1.16  fof(f8557,plain,(
% 5.90/1.16    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl12_49 | ~spl12_122)),
% 5.90/1.16    inference(forward_demodulation,[],[f8556,f111])).
% 5.90/1.16  fof(f111,plain,(
% 5.90/1.16    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.90/1.16    inference(equality_resolution,[],[f54])).
% 5.90/1.16  fof(f54,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f11])).
% 5.90/1.16  fof(f11,axiom,(
% 5.90/1.16    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.90/1.16  fof(f8556,plain,(
% 5.90/1.16    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | (spl12_49 | ~spl12_122)),
% 5.90/1.16    inference(forward_demodulation,[],[f1774,f8267])).
% 5.90/1.16  fof(f8267,plain,(
% 5.90/1.16    k1_xboole_0 = k1_relat_1(sK2) | ~spl12_122),
% 5.90/1.16    inference(avatar_component_clause,[],[f8265])).
% 5.90/1.16  fof(f1774,plain,(
% 5.90/1.16    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0) | spl12_49),
% 5.90/1.16    inference(avatar_component_clause,[],[f1772])).
% 5.90/1.16  fof(f8684,plain,(
% 5.90/1.16    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | r1_tarski(k1_xboole_0,k1_xboole_0)),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8608,plain,(
% 5.90/1.16    ~spl12_46 | ~spl12_47),
% 5.90/1.16    inference(avatar_contradiction_clause,[],[f8603])).
% 5.90/1.16  fof(f8603,plain,(
% 5.90/1.16    $false | (~spl12_46 | ~spl12_47)),
% 5.90/1.16    inference(unit_resulting_resolution,[],[f1613,f104,f1629,f42])).
% 5.90/1.16  fof(f42,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f26])).
% 5.90/1.16  fof(f26,plain,(
% 5.90/1.16    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 5.90/1.16    inference(ennf_transformation,[],[f1])).
% 5.90/1.16  fof(f1,axiom,(
% 5.90/1.16    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 5.90/1.16  fof(f1629,plain,(
% 5.90/1.16    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl12_47),
% 5.90/1.16    inference(avatar_component_clause,[],[f1627])).
% 5.90/1.16  fof(f1627,plain,(
% 5.90/1.16    spl12_47 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).
% 5.90/1.16  fof(f104,plain,(
% 5.90/1.16    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.90/1.16    inference(equality_resolution,[],[f40])).
% 5.90/1.16  fof(f40,plain,(
% 5.90/1.16    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f3])).
% 5.90/1.16  fof(f3,axiom,(
% 5.90/1.16    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.90/1.16  fof(f1613,plain,(
% 5.90/1.16    ( ! [X6] : (~r2_hidden(X6,k2_relat_1(sK2))) ) | ~spl12_46),
% 5.90/1.16    inference(avatar_component_clause,[],[f1612])).
% 5.90/1.16  fof(f1612,plain,(
% 5.90/1.16    spl12_46 <=> ! [X6] : ~r2_hidden(X6,k2_relat_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).
% 5.90/1.16  fof(f8544,plain,(
% 5.90/1.16    spl12_9 | ~spl12_72 | ~spl12_122),
% 5.90/1.16    inference(avatar_split_clause,[],[f8491,f8265,f2840,f257])).
% 5.90/1.16  fof(f257,plain,(
% 5.90/1.16    spl12_9 <=> r1_tarski(sK2,k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 5.90/1.16  fof(f2840,plain,(
% 5.90/1.16    spl12_72 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).
% 5.90/1.16  fof(f8491,plain,(
% 5.90/1.16    r1_tarski(sK2,k1_xboole_0) | (~spl12_72 | ~spl12_122)),
% 5.90/1.16    inference(forward_demodulation,[],[f8490,f111])).
% 5.90/1.16  fof(f8490,plain,(
% 5.90/1.16    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK2)) | (~spl12_72 | ~spl12_122)),
% 5.90/1.16    inference(forward_demodulation,[],[f2842,f8267])).
% 5.90/1.16  fof(f2842,plain,(
% 5.90/1.16    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2)) | ~spl12_72),
% 5.90/1.16    inference(avatar_component_clause,[],[f2840])).
% 5.90/1.16  fof(f8481,plain,(
% 5.90/1.16    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | sK0 != k1_setfam_1(sK2) | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,sK2) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(sK2,sK2)),k2_relat_1(sK2))),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8477,plain,(
% 5.90/1.16    sK0 != k1_setfam_1(sK2) | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | r1_tarski(k1_relat_1(k2_zfmisc_1(sK2,sK2)),k2_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),sK2)),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8476,plain,(
% 5.90/1.16    ~spl12_62 | ~spl12_27 | spl12_64),
% 5.90/1.16    inference(avatar_split_clause,[],[f6898,f2358,f661,f2317])).
% 5.90/1.16  fof(f2317,plain,(
% 5.90/1.16    spl12_62 <=> r2_hidden(sK0,sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).
% 5.90/1.16  fof(f661,plain,(
% 5.90/1.16    spl12_27 <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).
% 5.90/1.16  fof(f2358,plain,(
% 5.90/1.16    spl12_64 <=> r1_tarski(k1_relat_1(sK2),sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).
% 5.90/1.16  fof(f6898,plain,(
% 5.90/1.16    ~r2_hidden(sK0,sK2) | (~spl12_27 | spl12_64)),
% 5.90/1.16    inference(resolution,[],[f2360,f1721])).
% 5.90/1.16  fof(f1721,plain,(
% 5.90/1.16    ( ! [X1] : (r1_tarski(k1_relat_1(sK2),X1) | ~r2_hidden(sK0,X1)) ) | ~spl12_27),
% 5.90/1.16    inference(duplicate_literal_removal,[],[f1720])).
% 5.90/1.16  fof(f1720,plain,(
% 5.90/1.16    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(k1_relat_1(sK2),X1) | r1_tarski(k1_relat_1(sK2),X1)) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f44,f1564])).
% 5.90/1.16  fof(f1564,plain,(
% 5.90/1.16    ( ! [X6] : (sK0 = sK3(k1_relat_1(sK2),X6) | r1_tarski(k1_relat_1(sK2),X6)) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1554,f43])).
% 5.90/1.16  fof(f43,plain,(
% 5.90/1.16    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f26])).
% 5.90/1.16  fof(f1554,plain,(
% 5.90/1.16    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1543,f108])).
% 5.90/1.16  fof(f108,plain,(
% 5.90/1.16    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 5.90/1.16    inference(equality_resolution,[],[f50])).
% 5.90/1.16  fof(f50,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f18])).
% 5.90/1.16  fof(f18,axiom,(
% 5.90/1.16    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 5.90/1.16  fof(f1543,plain,(
% 5.90/1.16    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f103,f663])).
% 5.90/1.16  fof(f663,plain,(
% 5.90/1.16    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl12_27),
% 5.90/1.16    inference(avatar_component_clause,[],[f661])).
% 5.90/1.16  fof(f103,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X0 = X2) )),
% 5.90/1.16    inference(definition_unfolding,[],[f73,f79,f79])).
% 5.90/1.16  fof(f79,plain,(
% 5.90/1.16    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 5.90/1.16    inference(definition_unfolding,[],[f34,f76])).
% 5.90/1.16  fof(f76,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 5.90/1.16    inference(definition_unfolding,[],[f37,f58])).
% 5.90/1.16  fof(f58,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f9])).
% 5.90/1.16  fof(f9,axiom,(
% 5.90/1.16    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.90/1.16  fof(f37,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f8])).
% 5.90/1.16  fof(f8,axiom,(
% 5.90/1.16    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.90/1.16  fof(f34,plain,(
% 5.90/1.16    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f7])).
% 5.90/1.16  fof(f7,axiom,(
% 5.90/1.16    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.90/1.16  fof(f73,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 5.90/1.16    inference(cnf_transformation,[],[f13])).
% 5.90/1.16  fof(f13,axiom,(
% 5.90/1.16    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 5.90/1.16  fof(f44,plain,(
% 5.90/1.16    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f26])).
% 5.90/1.16  fof(f2360,plain,(
% 5.90/1.16    ~r1_tarski(k1_relat_1(sK2),sK2) | spl12_64),
% 5.90/1.16    inference(avatar_component_clause,[],[f2358])).
% 5.90/1.16  fof(f8335,plain,(
% 5.90/1.16    sK2 != k2_relat_1(k1_xboole_0) | sK0 != k1_setfam_1(sK2) | sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0))),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8331,plain,(
% 5.90/1.16    k1_xboole_0 != k1_relat_1(sK2) | sK2 != k2_relat_1(k1_xboole_0) | ~r1_tarski(sK2,k1_xboole_0) | r1_tarski(sK2,k1_relat_1(sK2))),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8302,plain,(
% 5.90/1.16    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f8298,plain,(
% 5.90/1.16    spl12_122 | spl12_4 | ~spl12_121),
% 5.90/1.16    inference(avatar_split_clause,[],[f8273,f8261,f133,f8265])).
% 5.90/1.16  fof(f133,plain,(
% 5.90/1.16    spl12_4 <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 5.90/1.16  fof(f8261,plain,(
% 5.90/1.16    spl12_121 <=> sK0 = sK10(k1_relat_1(sK2),sK0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_121])])).
% 5.90/1.16  fof(f8273,plain,(
% 5.90/1.16    k1_xboole_0 = k1_relat_1(sK2) | (spl12_4 | ~spl12_121)),
% 5.90/1.16    inference(trivial_inequality_removal,[],[f8270])).
% 5.90/1.16  fof(f8270,plain,(
% 5.90/1.16    sK0 != sK0 | k1_xboole_0 = k1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | (spl12_4 | ~spl12_121)),
% 5.90/1.16    inference(superposition,[],[f2151,f8263])).
% 5.90/1.16  fof(f8263,plain,(
% 5.90/1.16    sK0 = sK10(k1_relat_1(sK2),sK0) | ~spl12_121),
% 5.90/1.16    inference(avatar_component_clause,[],[f8261])).
% 5.90/1.16  fof(f2151,plain,(
% 5.90/1.16    ( ! [X1] : (sK0 != sK10(X1,sK0) | k1_xboole_0 = X1 | k1_relat_1(sK2) != X1) ) | spl12_4),
% 5.90/1.16    inference(superposition,[],[f135,f85])).
% 5.90/1.16  fof(f85,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | sK10(X0,X1) != X1) )),
% 5.90/1.16    inference(definition_unfolding,[],[f57,f79])).
% 5.90/1.16  fof(f57,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK10(X0,X1) != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f27])).
% 5.90/1.16  fof(f27,plain,(
% 5.90/1.16    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 5.90/1.16    inference(ennf_transformation,[],[f10])).
% 5.90/1.16  fof(f10,axiom,(
% 5.90/1.16    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 5.90/1.16  fof(f135,plain,(
% 5.90/1.16    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | spl12_4),
% 5.90/1.16    inference(avatar_component_clause,[],[f133])).
% 5.90/1.16  fof(f8268,plain,(
% 5.90/1.16    spl12_121 | spl12_122 | spl12_4 | ~spl12_27),
% 5.90/1.16    inference(avatar_split_clause,[],[f2263,f661,f133,f8265,f8261])).
% 5.90/1.16  fof(f2263,plain,(
% 5.90/1.16    k1_xboole_0 = k1_relat_1(sK2) | sK0 = sK10(k1_relat_1(sK2),sK0) | (spl12_4 | ~spl12_27)),
% 5.90/1.16    inference(trivial_inequality_removal,[],[f2255])).
% 5.90/1.16  fof(f2255,plain,(
% 5.90/1.16    k1_xboole_0 = k1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 = sK10(k1_relat_1(sK2),sK0) | (spl12_4 | ~spl12_27)),
% 5.90/1.16    inference(resolution,[],[f2150,f1554])).
% 5.90/1.16  fof(f2150,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(sK10(X0,sK0),X0) | k1_xboole_0 = X0 | k1_relat_1(sK2) != X0) ) | spl12_4),
% 5.90/1.16    inference(superposition,[],[f135,f86])).
% 5.90/1.16  fof(f86,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK10(X0,X1),X0)) )),
% 5.90/1.16    inference(definition_unfolding,[],[f56,f79])).
% 5.90/1.16  fof(f56,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK10(X0,X1),X0)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f27])).
% 5.90/1.16  fof(f6846,plain,(
% 5.90/1.16    sK2 != k2_relat_1(k1_xboole_0) | sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | r1_tarski(sK2,k1_relat_1(sK2)) | ~r1_tarski(sK2,k2_relat_1(k1_xboole_0))),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f6845,plain,(
% 5.90/1.16    ~spl12_67 | ~spl12_58 | spl12_66),
% 5.90/1.16    inference(avatar_split_clause,[],[f6827,f2567,f2099,f2575])).
% 5.90/1.16  fof(f2575,plain,(
% 5.90/1.16    spl12_67 <=> k1_xboole_0 = sK2),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_67])])).
% 5.90/1.16  fof(f2099,plain,(
% 5.90/1.16    spl12_58 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).
% 5.90/1.16  fof(f2567,plain,(
% 5.90/1.16    spl12_66 <=> sK2 = k2_relat_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_66])])).
% 5.90/1.16  fof(f6827,plain,(
% 5.90/1.16    k1_xboole_0 != sK2 | (~spl12_58 | spl12_66)),
% 5.90/1.16    inference(backward_demodulation,[],[f2568,f2101])).
% 5.90/1.16  fof(f2101,plain,(
% 5.90/1.16    k1_xboole_0 = k2_relat_1(sK2) | ~spl12_58),
% 5.90/1.16    inference(avatar_component_clause,[],[f2099])).
% 5.90/1.16  fof(f2568,plain,(
% 5.90/1.16    sK2 != k2_relat_1(sK2) | spl12_66),
% 5.90/1.16    inference(avatar_component_clause,[],[f2567])).
% 5.90/1.16  fof(f6844,plain,(
% 5.90/1.16    ~spl12_9 | ~spl12_50 | spl12_67),
% 5.90/1.16    inference(avatar_contradiction_clause,[],[f6841])).
% 5.90/1.16  fof(f6841,plain,(
% 5.90/1.16    $false | (~spl12_9 | ~spl12_50 | spl12_67)),
% 5.90/1.16    inference(unit_resulting_resolution,[],[f2577,f258,f1858,f41])).
% 5.90/1.16  fof(f41,plain,(
% 5.90/1.16    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f3])).
% 5.90/1.16  fof(f1858,plain,(
% 5.90/1.16    r1_tarski(k1_xboole_0,sK2) | ~spl12_50),
% 5.90/1.16    inference(avatar_component_clause,[],[f1857])).
% 5.90/1.16  fof(f1857,plain,(
% 5.90/1.16    spl12_50 <=> r1_tarski(k1_xboole_0,sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).
% 5.90/1.16  fof(f258,plain,(
% 5.90/1.16    r1_tarski(sK2,k1_xboole_0) | ~spl12_9),
% 5.90/1.16    inference(avatar_component_clause,[],[f257])).
% 5.90/1.16  fof(f2577,plain,(
% 5.90/1.16    k1_xboole_0 != sK2 | spl12_67),
% 5.90/1.16    inference(avatar_component_clause,[],[f2575])).
% 5.90/1.16  fof(f6839,plain,(
% 5.90/1.16    spl12_50 | ~spl12_38 | ~spl12_58),
% 5.90/1.16    inference(avatar_split_clause,[],[f6836,f2099,f1320,f1857])).
% 5.90/1.16  fof(f1320,plain,(
% 5.90/1.16    spl12_38 <=> r1_tarski(k2_relat_1(sK2),sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).
% 5.90/1.16  fof(f6836,plain,(
% 5.90/1.16    r1_tarski(k1_xboole_0,sK2) | (~spl12_38 | ~spl12_58)),
% 5.90/1.16    inference(forward_demodulation,[],[f1321,f2101])).
% 5.90/1.16  fof(f1321,plain,(
% 5.90/1.16    r1_tarski(k2_relat_1(sK2),sK2) | ~spl12_38),
% 5.90/1.16    inference(avatar_component_clause,[],[f1320])).
% 5.90/1.16  fof(f6715,plain,(
% 5.90/1.16    sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | sK2 != k2_relat_1(sK2) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f6714,plain,(
% 5.90/1.16    sK0 != k1_setfam_1(sK2) | sK1 != k1_setfam_1(sK2) | k4_tarski(sK0,sK1) != k1_setfam_1(sK2) | sK2 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | sK2 != k2_relat_1(sK2) | sK2 != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.90/1.16    introduced(theory_tautology_sat_conflict,[])).
% 5.90/1.16  fof(f2843,plain,(
% 5.90/1.16    ~spl12_1 | spl12_72 | ~spl12_66),
% 5.90/1.16    inference(avatar_split_clause,[],[f2573,f2567,f2840,f119])).
% 5.90/1.16  fof(f119,plain,(
% 5.90/1.16    spl12_1 <=> v1_relat_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 5.90/1.16  fof(f2573,plain,(
% 5.90/1.16    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK2)) | ~v1_relat_1(sK2) | ~spl12_66),
% 5.90/1.16    inference(superposition,[],[f35,f2569])).
% 5.90/1.16  fof(f2569,plain,(
% 5.90/1.16    sK2 = k2_relat_1(sK2) | ~spl12_66),
% 5.90/1.16    inference(avatar_component_clause,[],[f2567])).
% 5.90/1.16  fof(f35,plain,(
% 5.90/1.16    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f25])).
% 5.90/1.16  fof(f25,plain,(
% 5.90/1.16    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 5.90/1.16    inference(ennf_transformation,[],[f20])).
% 5.90/1.16  fof(f20,axiom,(
% 5.90/1.16    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 5.90/1.16  fof(f2715,plain,(
% 5.90/1.16    ~spl12_69 | ~spl12_12 | ~spl12_45),
% 5.90/1.16    inference(avatar_split_clause,[],[f2706,f1608,f351,f2712])).
% 5.90/1.16  fof(f2712,plain,(
% 5.90/1.16    spl12_69 <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).
% 5.90/1.16  fof(f351,plain,(
% 5.90/1.16    spl12_12 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 5.90/1.16  fof(f1608,plain,(
% 5.90/1.16    spl12_45 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).
% 5.90/1.16  fof(f2706,plain,(
% 5.90/1.16    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl12_12 | ~spl12_45)),
% 5.90/1.16    inference(resolution,[],[f2446,f1610])).
% 5.90/1.16  fof(f1610,plain,(
% 5.90/1.16    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl12_45),
% 5.90/1.16    inference(avatar_component_clause,[],[f1608])).
% 5.90/1.16  fof(f2446,plain,(
% 5.90/1.16    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_xboole_0)) ) | ~spl12_12),
% 5.90/1.16    inference(resolution,[],[f352,f42])).
% 5.90/1.16  fof(f352,plain,(
% 5.90/1.16    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl12_12),
% 5.90/1.16    inference(avatar_component_clause,[],[f351])).
% 5.90/1.16  fof(f2578,plain,(
% 5.90/1.16    ~spl12_67 | spl12_58 | ~spl12_66),
% 5.90/1.16    inference(avatar_split_clause,[],[f2571,f2567,f2099,f2575])).
% 5.90/1.16  fof(f2571,plain,(
% 5.90/1.16    k1_xboole_0 != sK2 | (spl12_58 | ~spl12_66)),
% 5.90/1.16    inference(superposition,[],[f2100,f2569])).
% 5.90/1.16  fof(f2100,plain,(
% 5.90/1.16    k1_xboole_0 != k2_relat_1(sK2) | spl12_58),
% 5.90/1.16    inference(avatar_component_clause,[],[f2099])).
% 5.90/1.16  fof(f2570,plain,(
% 5.90/1.16    spl12_66 | ~spl12_3 | ~spl12_6 | ~spl12_29),
% 5.90/1.16    inference(avatar_split_clause,[],[f2551,f763,f176,f129,f2567])).
% 5.90/1.16  fof(f129,plain,(
% 5.90/1.16    spl12_3 <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 5.90/1.16  fof(f176,plain,(
% 5.90/1.16    spl12_6 <=> sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 5.90/1.16  fof(f763,plain,(
% 5.90/1.16    spl12_29 <=> sK1 = k1_setfam_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 5.90/1.16  fof(f2551,plain,(
% 5.90/1.16    sK2 = k2_relat_1(sK2) | (~spl12_3 | ~spl12_6 | ~spl12_29)),
% 5.90/1.16    inference(backward_demodulation,[],[f130,f2509])).
% 5.90/1.16  fof(f2509,plain,(
% 5.90/1.16    sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl12_6 | ~spl12_29)),
% 5.90/1.16    inference(backward_demodulation,[],[f178,f765])).
% 5.90/1.16  fof(f765,plain,(
% 5.90/1.16    sK1 = k1_setfam_1(sK2) | ~spl12_29),
% 5.90/1.16    inference(avatar_component_clause,[],[f763])).
% 5.90/1.16  fof(f178,plain,(
% 5.90/1.16    sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2)) | ~spl12_6),
% 5.90/1.16    inference(avatar_component_clause,[],[f176])).
% 5.90/1.16  fof(f130,plain,(
% 5.90/1.16    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl12_3),
% 5.90/1.16    inference(avatar_component_clause,[],[f129])).
% 5.90/1.16  fof(f2561,plain,(
% 5.90/1.16    ~spl12_31 | ~spl12_27 | spl12_38),
% 5.90/1.16    inference(avatar_split_clause,[],[f1737,f1320,f661,f802])).
% 5.90/1.16  fof(f802,plain,(
% 5.90/1.16    spl12_31 <=> r2_hidden(sK1,sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 5.90/1.16  fof(f1737,plain,(
% 5.90/1.16    ~r2_hidden(sK1,sK2) | (~spl12_27 | spl12_38)),
% 5.90/1.16    inference(resolution,[],[f1735,f1322])).
% 5.90/1.16  fof(f1322,plain,(
% 5.90/1.16    ~r1_tarski(k2_relat_1(sK2),sK2) | spl12_38),
% 5.90/1.16    inference(avatar_component_clause,[],[f1320])).
% 5.90/1.16  fof(f1735,plain,(
% 5.90/1.16    ( ! [X1] : (r1_tarski(k2_relat_1(sK2),X1) | ~r2_hidden(sK1,X1)) ) | ~spl12_27),
% 5.90/1.16    inference(duplicate_literal_removal,[],[f1734])).
% 5.90/1.16  fof(f1734,plain,(
% 5.90/1.16    ( ! [X1] : (~r2_hidden(sK1,X1) | r1_tarski(k2_relat_1(sK2),X1) | r1_tarski(k2_relat_1(sK2),X1)) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f44,f1580])).
% 5.90/1.16  fof(f1580,plain,(
% 5.90/1.16    ( ! [X6] : (sK1 = sK3(k2_relat_1(sK2),X6) | r1_tarski(k2_relat_1(sK2),X6)) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1568,f43])).
% 5.90/1.16  fof(f1568,plain,(
% 5.90/1.16    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | sK1 = X1) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1544,f106])).
% 5.90/1.16  fof(f106,plain,(
% 5.90/1.16    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 5.90/1.16    inference(equality_resolution,[],[f46])).
% 5.90/1.16  fof(f46,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f19])).
% 5.90/1.16  fof(f19,axiom,(
% 5.90/1.16    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 5.90/1.16  fof(f1544,plain,(
% 5.90/1.16    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | sK1 = X3) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f102,f663])).
% 5.90/1.16  fof(f102,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 5.90/1.16    inference(definition_unfolding,[],[f74,f79,f79])).
% 5.90/1.16  fof(f74,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 5.90/1.16    inference(cnf_transformation,[],[f13])).
% 5.90/1.16  fof(f2458,plain,(
% 5.90/1.16    ~spl12_12 | ~spl12_61),
% 5.90/1.16    inference(avatar_contradiction_clause,[],[f2454])).
% 5.90/1.16  fof(f2454,plain,(
% 5.90/1.16    $false | (~spl12_12 | ~spl12_61)),
% 5.90/1.16    inference(resolution,[],[f352,f2184])).
% 5.90/1.16  fof(f2184,plain,(
% 5.90/1.16    r2_hidden(sK1,k1_xboole_0) | ~spl12_61),
% 5.90/1.16    inference(avatar_component_clause,[],[f2182])).
% 5.90/1.16  fof(f2182,plain,(
% 5.90/1.16    spl12_61 <=> r2_hidden(sK1,k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).
% 5.90/1.16  fof(f2423,plain,(
% 5.90/1.16    ~spl12_1 | spl12_9 | ~spl12_58),
% 5.90/1.16    inference(avatar_split_clause,[],[f2422,f2099,f257,f119])).
% 5.90/1.16  fof(f2422,plain,(
% 5.90/1.16    r1_tarski(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | ~spl12_58),
% 5.90/1.16    inference(forward_demodulation,[],[f2421,f110])).
% 5.90/1.16  fof(f110,plain,(
% 5.90/1.16    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.90/1.16    inference(equality_resolution,[],[f55])).
% 5.90/1.16  fof(f55,plain,(
% 5.90/1.16    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f11])).
% 5.90/1.16  fof(f2421,plain,(
% 5.90/1.16    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~v1_relat_1(sK2) | ~spl12_58),
% 5.90/1.16    inference(superposition,[],[f35,f2101])).
% 5.90/1.16  fof(f2416,plain,(
% 5.90/1.16    spl12_58 | spl12_3 | ~spl12_59),
% 5.90/1.16    inference(avatar_split_clause,[],[f2397,f2103,f129,f2099])).
% 5.90/1.16  fof(f2103,plain,(
% 5.90/1.16    spl12_59 <=> sK1 = sK10(k2_relat_1(sK2),sK1)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).
% 5.90/1.16  fof(f2397,plain,(
% 5.90/1.16    k1_xboole_0 = k2_relat_1(sK2) | (spl12_3 | ~spl12_59)),
% 5.90/1.16    inference(trivial_inequality_removal,[],[f2396])).
% 5.90/1.16  fof(f2396,plain,(
% 5.90/1.16    sK1 != sK1 | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relat_1(sK2) | (spl12_3 | ~spl12_59)),
% 5.90/1.16    inference(superposition,[],[f2213,f2105])).
% 5.90/1.16  fof(f2105,plain,(
% 5.90/1.16    sK1 = sK10(k2_relat_1(sK2),sK1) | ~spl12_59),
% 5.90/1.16    inference(avatar_component_clause,[],[f2103])).
% 5.90/1.16  fof(f2213,plain,(
% 5.90/1.16    ( ! [X1] : (sK1 != sK10(X1,sK1) | k1_xboole_0 = X1 | k2_relat_1(sK2) != X1) ) | spl12_3),
% 5.90/1.16    inference(superposition,[],[f131,f85])).
% 5.90/1.16  fof(f131,plain,(
% 5.90/1.16    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | spl12_3),
% 5.90/1.16    inference(avatar_component_clause,[],[f129])).
% 5.90/1.16  fof(f2207,plain,(
% 5.90/1.16    ~spl12_5 | ~spl12_20 | ~spl12_48),
% 5.90/1.16    inference(avatar_contradiction_clause,[],[f2192])).
% 5.90/1.16  fof(f2192,plain,(
% 5.90/1.16    $false | (~spl12_5 | ~spl12_20 | ~spl12_48)),
% 5.90/1.16    inference(unit_resulting_resolution,[],[f594,f1632,f189])).
% 5.90/1.16  fof(f189,plain,(
% 5.90/1.16    ( ! [X13] : (r2_hidden(sK0,k1_relat_1(X13)) | ~r2_hidden(k1_setfam_1(sK2),X13)) ) | ~spl12_5),
% 5.90/1.16    inference(superposition,[],[f109,f173])).
% 5.90/1.16  fof(f173,plain,(
% 5.90/1.16    k4_tarski(sK0,sK1) = k1_setfam_1(sK2) | ~spl12_5),
% 5.90/1.16    inference(avatar_component_clause,[],[f171])).
% 5.90/1.16  fof(f171,plain,(
% 5.90/1.16    spl12_5 <=> k4_tarski(sK0,sK1) = k1_setfam_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 5.90/1.16  fof(f109,plain,(
% 5.90/1.16    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 5.90/1.16    inference(equality_resolution,[],[f49])).
% 5.90/1.16  fof(f49,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f18])).
% 5.90/1.16  fof(f1632,plain,(
% 5.90/1.16    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2))) ) | ~spl12_48),
% 5.90/1.16    inference(avatar_component_clause,[],[f1631])).
% 5.90/1.16  fof(f1631,plain,(
% 5.90/1.16    spl12_48 <=> ! [X7] : ~r2_hidden(X7,k1_relat_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).
% 5.90/1.16  fof(f594,plain,(
% 5.90/1.16    r2_hidden(k1_setfam_1(sK2),sK2) | ~spl12_20),
% 5.90/1.16    inference(avatar_component_clause,[],[f592])).
% 5.90/1.16  fof(f592,plain,(
% 5.90/1.16    spl12_20 <=> r2_hidden(k1_setfam_1(sK2),sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 5.90/1.16  fof(f2185,plain,(
% 5.90/1.16    spl12_61 | ~spl12_47 | ~spl12_58),
% 5.90/1.16    inference(avatar_split_clause,[],[f2170,f2099,f1627,f2182])).
% 5.90/1.16  fof(f2170,plain,(
% 5.90/1.16    r2_hidden(sK1,k1_xboole_0) | (~spl12_47 | ~spl12_58)),
% 5.90/1.16    inference(backward_demodulation,[],[f1629,f2101])).
% 5.90/1.16  fof(f2106,plain,(
% 5.90/1.16    spl12_58 | spl12_59 | spl12_3 | ~spl12_27),
% 5.90/1.16    inference(avatar_split_clause,[],[f1583,f661,f129,f2103,f2099])).
% 5.90/1.16  fof(f1583,plain,(
% 5.90/1.16    sK1 = sK10(k2_relat_1(sK2),sK1) | k1_xboole_0 = k2_relat_1(sK2) | (spl12_3 | ~spl12_27)),
% 5.90/1.16    inference(trivial_inequality_removal,[],[f1581])).
% 5.90/1.16  fof(f1581,plain,(
% 5.90/1.16    sK1 = sK10(k2_relat_1(sK2),sK1) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relat_1(sK2) | (spl12_3 | ~spl12_27)),
% 5.90/1.16    inference(resolution,[],[f1568,f137])).
% 5.90/1.16  fof(f137,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(sK10(X0,sK1),X0) | k1_xboole_0 = X0 | k2_relat_1(sK2) != X0) ) | spl12_3),
% 5.90/1.16    inference(superposition,[],[f131,f86])).
% 5.90/1.16  fof(f1775,plain,(
% 5.90/1.16    ~spl12_1 | ~spl12_49 | ~spl12_6 | ~spl12_30),
% 5.90/1.16    inference(avatar_split_clause,[],[f1479,f767,f176,f1772,f119])).
% 5.90/1.16  fof(f767,plain,(
% 5.90/1.16    spl12_30 <=> ! [X0] : ~r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 5.90/1.16  fof(f1479,plain,(
% 5.90/1.16    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_xboole_0) | ~v1_relat_1(sK2) | (~spl12_6 | ~spl12_30)),
% 5.90/1.16    inference(resolution,[],[f1455,f35])).
% 5.90/1.16  fof(f1455,plain,(
% 5.90/1.16    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl12_6 | ~spl12_30)),
% 5.90/1.16    inference(resolution,[],[f927,f826])).
% 5.90/1.16  fof(f826,plain,(
% 5.90/1.16    ( ! [X28] : (r2_hidden(k1_setfam_1(sK2),X28) | ~r1_tarski(sK2,X28)) ) | ~spl12_6),
% 5.90/1.16    inference(superposition,[],[f96,f178])).
% 5.90/1.16  fof(f96,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 5.90/1.16    inference(definition_unfolding,[],[f68,f76])).
% 5.90/1.16  fof(f68,plain,(
% 5.90/1.16    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 5.90/1.16    inference(cnf_transformation,[],[f15])).
% 5.90/1.16  fof(f15,axiom,(
% 5.90/1.16    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 5.90/1.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 5.90/1.16  fof(f927,plain,(
% 5.90/1.16    ( ! [X0] : (~r2_hidden(k1_setfam_1(sK2),X0) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl12_30),
% 5.90/1.16    inference(superposition,[],[f847,f111])).
% 5.90/1.16  fof(f847,plain,(
% 5.90/1.16    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,sK2)) | ~r2_hidden(k1_setfam_1(sK2),X0)) ) | ~spl12_30),
% 5.90/1.16    inference(resolution,[],[f768,f42])).
% 5.90/1.16  fof(f768,plain,(
% 5.90/1.16    ( ! [X0] : (~r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2))) ) | ~spl12_30),
% 5.90/1.16    inference(avatar_component_clause,[],[f767])).
% 5.90/1.16  fof(f1633,plain,(
% 5.90/1.16    spl12_47 | spl12_48 | ~spl12_27),
% 5.90/1.16    inference(avatar_split_clause,[],[f1624,f661,f1631,f1627])).
% 5.90/1.16  fof(f1624,plain,(
% 5.90/1.16    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | r2_hidden(sK1,k2_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1587,f107])).
% 5.90/1.16  fof(f107,plain,(
% 5.90/1.16    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 5.90/1.16    inference(equality_resolution,[],[f45])).
% 5.90/1.16  fof(f45,plain,(
% 5.90/1.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 5.90/1.16    inference(cnf_transformation,[],[f19])).
% 5.90/1.16  fof(f1587,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(duplicate_literal_removal,[],[f1586])).
% 5.90/1.16  fof(f1586,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f108,f1570])).
% 5.90/1.16  fof(f1570,plain,(
% 5.90/1.16    ( ! [X3] : (sK1 = sK8(sK2,X3) | ~r2_hidden(X3,k1_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1544,f108])).
% 5.90/1.16  fof(f1614,plain,(
% 5.90/1.16    spl12_45 | spl12_46 | ~spl12_27),
% 5.90/1.16    inference(avatar_split_clause,[],[f1604,f661,f1612,f1608])).
% 5.90/1.16  fof(f1604,plain,(
% 5.90/1.16    ( ! [X6] : (~r2_hidden(X6,k2_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1585,f109])).
% 5.90/1.16  fof(f1585,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(duplicate_literal_removal,[],[f1584])).
% 5.90/1.16  fof(f1584,plain,(
% 5.90/1.16    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(superposition,[],[f106,f1552])).
% 5.90/1.16  fof(f1552,plain,(
% 5.90/1.16    ( ! [X1] : (sK0 = sK5(sK2,X1) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl12_27),
% 5.90/1.16    inference(resolution,[],[f1543,f106])).
% 5.90/1.16  fof(f1596,plain,(
% 5.90/1.16    ~spl12_43 | spl12_44 | ~spl12_6 | ~spl12_27),
% 5.90/1.16    inference(avatar_split_clause,[],[f1562,f661,f176,f1593,f1589])).
% 5.90/1.16  fof(f1589,plain,(
% 5.90/1.16    spl12_43 <=> r1_tarski(sK2,k1_relat_1(sK2))),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).
% 5.90/1.16  fof(f1593,plain,(
% 5.90/1.16    spl12_44 <=> sK0 = k1_setfam_1(sK2)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).
% 5.90/1.16  fof(f1562,plain,(
% 5.90/1.16    sK0 = k1_setfam_1(sK2) | ~r1_tarski(sK2,k1_relat_1(sK2)) | (~spl12_6 | ~spl12_27)),
% 5.90/1.16    inference(resolution,[],[f1554,f826])).
% 5.90/1.16  fof(f1429,plain,(
% 5.90/1.16    ~spl12_8 | ~spl12_30),
% 5.90/1.16    inference(avatar_split_clause,[],[f848,f767,f250])).
% 5.90/1.16  fof(f250,plain,(
% 5.90/1.16    spl12_8 <=> r2_hidden(k1_setfam_1(sK2),k1_xboole_0)),
% 5.90/1.16    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 5.90/1.16  fof(f848,plain,(
% 5.90/1.16    ~r2_hidden(k1_setfam_1(sK2),k1_xboole_0) | ~spl12_30),
% 5.90/1.16    inference(superposition,[],[f768,f111])).
% 5.90/1.16  fof(f1382,plain,(
% 5.90/1.16    ~spl12_6 | spl12_17 | ~spl12_20),
% 5.90/1.16    inference(avatar_contradiction_clause,[],[f1365])).
% 5.90/1.16  fof(f1365,plain,(
% 5.90/1.16    $false | (~spl12_6 | spl12_17 | ~spl12_20)),
% 5.90/1.16    inference(unit_resulting_resolution,[],[f530,f594,f1362])).
% 5.90/1.16  fof(f1362,plain,(
% 5.90/1.16    ( ! [X1] : (~r2_hidden(k1_setfam_1(sK2),X1) | r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | ~spl12_6),
% 5.90/1.16    inference(duplicate_literal_removal,[],[f1361])).
% 5.90/1.16  fof(f1361,plain,(
% 5.90/1.16    ( ! [X1] : (~r2_hidden(k1_setfam_1(sK2),X1) | r1_tarski(k2_relat_1(k1_xboole_0),X1) | r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | ~spl12_6),
% 5.90/1.16    inference(superposition,[],[f44,f297])).
% 5.90/1.17  fof(f297,plain,(
% 5.90/1.17    ( ! [X6] : (k1_setfam_1(sK2) = sK3(k2_relat_1(k1_xboole_0),X6) | r1_tarski(k2_relat_1(k1_xboole_0),X6)) ) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f285,f43])).
% 5.90/1.17  fof(f285,plain,(
% 5.90/1.17    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0)) | k1_setfam_1(sK2) = X1) ) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f283,f106])).
% 5.90/1.17  fof(f283,plain,(
% 5.90/1.17    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | k1_setfam_1(sK2) = X1) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f204,f111])).
% 5.90/1.17  fof(f204,plain,(
% 5.90/1.17    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(X4,sK2)) | k1_setfam_1(sK2) = X3) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f99,f178])).
% 5.90/1.17  fof(f99,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 5.90/1.17    inference(definition_unfolding,[],[f71,f79])).
% 5.90/1.17  fof(f71,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 5.90/1.17    inference(cnf_transformation,[],[f12])).
% 5.90/1.17  fof(f12,axiom,(
% 5.90/1.17    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 5.90/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 5.90/1.17  fof(f530,plain,(
% 5.90/1.17    ~r1_tarski(k2_relat_1(k1_xboole_0),sK2) | spl12_17),
% 5.90/1.17    inference(avatar_component_clause,[],[f528])).
% 5.90/1.17  fof(f528,plain,(
% 5.90/1.17    spl12_17 <=> r1_tarski(k2_relat_1(k1_xboole_0),sK2)),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 5.90/1.17  fof(f1329,plain,(
% 5.90/1.17    spl12_27 | ~spl12_2),
% 5.90/1.17    inference(avatar_split_clause,[],[f146,f124,f661])).
% 5.90/1.17  fof(f124,plain,(
% 5.90/1.17    spl12_2 <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 5.90/1.17  fof(f146,plain,(
% 5.90/1.17    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f88,f126])).
% 5.90/1.17  fof(f126,plain,(
% 5.90/1.17    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl12_2),
% 5.90/1.17    inference(avatar_component_clause,[],[f124])).
% 5.90/1.17  fof(f88,plain,(
% 5.90/1.17    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 5.90/1.17    inference(definition_unfolding,[],[f59,f79,f76,f76])).
% 5.90/1.17  fof(f59,plain,(
% 5.90/1.17    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 5.90/1.17    inference(cnf_transformation,[],[f14])).
% 5.90/1.17  fof(f14,axiom,(
% 5.90/1.17    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 5.90/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 5.90/1.17  fof(f805,plain,(
% 5.90/1.17    spl12_31 | ~spl12_20 | ~spl12_29),
% 5.90/1.17    inference(avatar_split_clause,[],[f795,f763,f592,f802])).
% 5.90/1.17  fof(f795,plain,(
% 5.90/1.17    r2_hidden(sK1,sK2) | (~spl12_20 | ~spl12_29)),
% 5.90/1.17    inference(backward_demodulation,[],[f594,f765])).
% 5.90/1.17  fof(f769,plain,(
% 5.90/1.17    spl12_29 | spl12_30 | ~spl12_5 | ~spl12_6),
% 5.90/1.17    inference(avatar_split_clause,[],[f282,f176,f171,f767,f763])).
% 5.90/1.17  fof(f282,plain,(
% 5.90/1.17    ( ! [X0] : (~r2_hidden(k1_setfam_1(sK2),k2_zfmisc_1(X0,sK2)) | sK1 = k1_setfam_1(sK2)) ) | (~spl12_5 | ~spl12_6)),
% 5.90/1.17    inference(superposition,[],[f204,f173])).
% 5.90/1.17  fof(f595,plain,(
% 5.90/1.17    spl12_20 | ~spl12_6),
% 5.90/1.17    inference(avatar_split_clause,[],[f582,f176,f592])).
% 5.90/1.17  fof(f582,plain,(
% 5.90/1.17    r2_hidden(k1_setfam_1(sK2),sK2) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f211,f100])).
% 5.90/1.17  fof(f100,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 5.90/1.17    inference(definition_unfolding,[],[f70,f79])).
% 5.90/1.17  fof(f70,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 5.90/1.17    inference(cnf_transformation,[],[f12])).
% 5.90/1.17  fof(f211,plain,(
% 5.90/1.17    ( ! [X22] : (r2_hidden(k4_tarski(k1_setfam_1(sK2),X22),k2_zfmisc_1(sK2,k2_enumset1(X22,X22,X22,X22)))) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f117,f178])).
% 5.90/1.17  fof(f117,plain,(
% 5.90/1.17    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 5.90/1.17    inference(equality_resolution,[],[f116])).
% 5.90/1.17  fof(f116,plain,(
% 5.90/1.17    ( ! [X2,X3,X1] : (X1 != X3 | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 5.90/1.17    inference(equality_resolution,[],[f101])).
% 5.90/1.17  fof(f101,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 5.90/1.17    inference(definition_unfolding,[],[f75,f79,f79])).
% 5.90/1.17  fof(f75,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 5.90/1.17    inference(cnf_transformation,[],[f13])).
% 5.90/1.17  fof(f567,plain,(
% 5.90/1.17    spl12_19 | ~spl12_6),
% 5.90/1.17    inference(avatar_split_clause,[],[f565,f176,f558])).
% 5.90/1.17  fof(f558,plain,(
% 5.90/1.17    spl12_19 <=> r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 5.90/1.17  fof(f565,plain,(
% 5.90/1.17    r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl12_6),
% 5.90/1.17    inference(duplicate_literal_removal,[],[f563])).
% 5.90/1.17  fof(f563,plain,(
% 5.90/1.17    r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f337,f43])).
% 5.90/1.17  fof(f337,plain,(
% 5.90/1.17    ( ! [X3] : (~r2_hidden(sK3(X3,k1_relat_1(k1_xboole_0)),k1_xboole_0) | r1_tarski(X3,k1_relat_1(k1_xboole_0))) ) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f332,f44])).
% 5.90/1.17  fof(f332,plain,(
% 5.90/1.17    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f321,f111])).
% 5.90/1.17  fof(f321,plain,(
% 5.90/1.17    ( ! [X6,X7] : (r2_hidden(X6,k1_relat_1(k2_zfmisc_1(X7,sK2))) | ~r2_hidden(X6,X7)) ) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f210,f109])).
% 5.90/1.17  fof(f210,plain,(
% 5.90/1.17    ( ! [X21,X20] : (r2_hidden(k4_tarski(X20,k1_setfam_1(sK2)),k2_zfmisc_1(X21,sK2)) | ~r2_hidden(X20,X21)) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f115,f178])).
% 5.90/1.17  fof(f115,plain,(
% 5.90/1.17    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 5.90/1.17    inference(equality_resolution,[],[f98])).
% 5.90/1.17  fof(f98,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) )),
% 5.90/1.17    inference(definition_unfolding,[],[f72,f79])).
% 5.90/1.17  fof(f72,plain,(
% 5.90/1.17    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 5.90/1.17    inference(cnf_transformation,[],[f12])).
% 5.90/1.17  fof(f561,plain,(
% 5.90/1.17    spl12_15 | ~spl12_19 | ~spl12_18),
% 5.90/1.17    inference(avatar_split_clause,[],[f556,f552,f558,f496])).
% 5.90/1.17  fof(f496,plain,(
% 5.90/1.17    spl12_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 5.90/1.17  fof(f552,plain,(
% 5.90/1.17    spl12_18 <=> r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 5.90/1.17  fof(f556,plain,(
% 5.90/1.17    ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl12_18),
% 5.90/1.17    inference(resolution,[],[f554,f41])).
% 5.90/1.17  fof(f554,plain,(
% 5.90/1.17    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl12_18),
% 5.90/1.17    inference(avatar_component_clause,[],[f552])).
% 5.90/1.17  fof(f555,plain,(
% 5.90/1.17    spl12_18 | ~spl12_2),
% 5.90/1.17    inference(avatar_split_clause,[],[f550,f124,f552])).
% 5.90/1.17  fof(f550,plain,(
% 5.90/1.17    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl12_2),
% 5.90/1.17    inference(duplicate_literal_removal,[],[f549])).
% 5.90/1.17  fof(f549,plain,(
% 5.90/1.17    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl12_2),
% 5.90/1.17    inference(resolution,[],[f243,f44])).
% 5.90/1.17  fof(f243,plain,(
% 5.90/1.17    ( ! [X6] : (r2_hidden(sK3(k1_relat_1(k1_xboole_0),X6),k1_xboole_0) | r1_tarski(k1_relat_1(k1_xboole_0),X6)) ) | ~spl12_2),
% 5.90/1.17    inference(resolution,[],[f233,f43])).
% 5.90/1.17  fof(f233,plain,(
% 5.90/1.17    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0)) | r2_hidden(X3,k1_xboole_0)) ) | ~spl12_2),
% 5.90/1.17    inference(resolution,[],[f229,f108])).
% 5.90/1.17  fof(f229,plain,(
% 5.90/1.17    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | r2_hidden(X0,k1_xboole_0)) ) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f151,f111])).
% 5.90/1.17  fof(f151,plain,(
% 5.90/1.17    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,sK2)) | r2_hidden(X5,X7)) ) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f100,f126])).
% 5.90/1.17  fof(f531,plain,(
% 5.90/1.17    spl12_16 | ~spl12_17 | ~spl12_14),
% 5.90/1.17    inference(avatar_split_clause,[],[f502,f371,f528,f524])).
% 5.90/1.17  fof(f524,plain,(
% 5.90/1.17    spl12_16 <=> sK2 = k2_relat_1(k1_xboole_0)),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 5.90/1.17  fof(f371,plain,(
% 5.90/1.17    spl12_14 <=> r1_tarski(sK2,k2_relat_1(k1_xboole_0))),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 5.90/1.17  fof(f502,plain,(
% 5.90/1.17    ~r1_tarski(k2_relat_1(k1_xboole_0),sK2) | sK2 = k2_relat_1(k1_xboole_0) | ~spl12_14),
% 5.90/1.17    inference(resolution,[],[f373,f41])).
% 5.90/1.17  fof(f373,plain,(
% 5.90/1.17    r1_tarski(sK2,k2_relat_1(k1_xboole_0)) | ~spl12_14),
% 5.90/1.17    inference(avatar_component_clause,[],[f371])).
% 5.90/1.17  fof(f374,plain,(
% 5.90/1.17    spl12_14 | ~spl12_2 | ~spl12_5 | ~spl12_11),
% 5.90/1.17    inference(avatar_split_clause,[],[f356,f347,f171,f124,f371])).
% 5.90/1.17  fof(f347,plain,(
% 5.90/1.17    spl12_11 <=> r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0))),
% 5.90/1.17    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 5.90/1.17  fof(f356,plain,(
% 5.90/1.17    r1_tarski(sK2,k2_relat_1(k1_xboole_0)) | (~spl12_2 | ~spl12_5 | ~spl12_11)),
% 5.90/1.17    inference(resolution,[],[f349,f194])).
% 5.90/1.17  fof(f194,plain,(
% 5.90/1.17    ( ! [X27] : (~r2_hidden(k1_setfam_1(sK2),X27) | r1_tarski(sK2,X27)) ) | (~spl12_2 | ~spl12_5)),
% 5.90/1.17    inference(forward_demodulation,[],[f168,f173])).
% 5.90/1.17  fof(f168,plain,(
% 5.90/1.17    ( ! [X27] : (r1_tarski(sK2,X27) | ~r2_hidden(k4_tarski(sK0,sK1),X27)) ) | ~spl12_2),
% 5.90/1.17    inference(duplicate_literal_removal,[],[f162])).
% 5.90/1.17  fof(f162,plain,(
% 5.90/1.17    ( ! [X27] : (r1_tarski(sK2,X27) | ~r2_hidden(k4_tarski(sK0,sK1),X27) | ~r2_hidden(k4_tarski(sK0,sK1),X27)) ) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f95,f126])).
% 5.90/1.17  fof(f95,plain,(
% 5.90/1.17    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 5.90/1.17    inference(definition_unfolding,[],[f69,f76])).
% 5.90/1.17  fof(f69,plain,(
% 5.90/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 5.90/1.17    inference(cnf_transformation,[],[f15])).
% 5.90/1.17  fof(f349,plain,(
% 5.90/1.17    r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0)) | ~spl12_11),
% 5.90/1.17    inference(avatar_component_clause,[],[f347])).
% 5.90/1.17  fof(f353,plain,(
% 5.90/1.17    spl12_11 | spl12_12 | ~spl12_6),
% 5.90/1.17    inference(avatar_split_clause,[],[f345,f176,f351,f347])).
% 5.90/1.17  fof(f345,plain,(
% 5.90/1.17    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(k1_setfam_1(sK2),k2_relat_1(k1_xboole_0))) ) | ~spl12_6),
% 5.90/1.17    inference(resolution,[],[f323,f107])).
% 5.90/1.17  fof(f323,plain,(
% 5.90/1.17    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_setfam_1(sK2)),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl12_6),
% 5.90/1.17    inference(superposition,[],[f210,f111])).
% 5.90/1.17  fof(f260,plain,(
% 5.90/1.17    ~spl12_9 | ~spl12_2 | ~spl12_5 | spl12_8),
% 5.90/1.17    inference(avatar_split_clause,[],[f254,f250,f171,f124,f257])).
% 5.90/1.17  fof(f254,plain,(
% 5.90/1.17    ~r1_tarski(sK2,k1_xboole_0) | (~spl12_2 | ~spl12_5 | spl12_8)),
% 5.90/1.17    inference(resolution,[],[f252,f192])).
% 5.90/1.17  fof(f192,plain,(
% 5.90/1.17    ( ! [X28] : (r2_hidden(k1_setfam_1(sK2),X28) | ~r1_tarski(sK2,X28)) ) | (~spl12_2 | ~spl12_5)),
% 5.90/1.17    inference(forward_demodulation,[],[f163,f173])).
% 5.90/1.17  fof(f163,plain,(
% 5.90/1.17    ( ! [X28] : (~r1_tarski(sK2,X28) | r2_hidden(k4_tarski(sK0,sK1),X28)) ) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f96,f126])).
% 5.90/1.17  fof(f252,plain,(
% 5.90/1.17    ~r2_hidden(k1_setfam_1(sK2),k1_xboole_0) | spl12_8),
% 5.90/1.17    inference(avatar_component_clause,[],[f250])).
% 5.90/1.17  fof(f179,plain,(
% 5.90/1.17    spl12_6 | ~spl12_2),
% 5.90/1.17    inference(avatar_split_clause,[],[f169,f124,f176])).
% 5.90/1.17  fof(f169,plain,(
% 5.90/1.17    sK2 = k2_enumset1(k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2),k1_setfam_1(sK2)) | ~spl12_2),
% 5.90/1.17    inference(backward_demodulation,[],[f126,f147])).
% 5.90/1.17  fof(f147,plain,(
% 5.90/1.17    k4_tarski(sK0,sK1) = k1_setfam_1(sK2) | ~spl12_2),
% 5.90/1.17    inference(superposition,[],[f83,f126])).
% 5.90/1.17  fof(f83,plain,(
% 5.90/1.17    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 5.90/1.17    inference(definition_unfolding,[],[f32,f79])).
% 5.90/1.17  fof(f32,plain,(
% 5.90/1.17    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 5.90/1.17    inference(cnf_transformation,[],[f16])).
% 5.90/1.17  fof(f16,axiom,(
% 5.90/1.17    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 5.90/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 5.90/1.17  fof(f174,plain,(
% 5.90/1.17    spl12_5 | ~spl12_2),
% 5.90/1.17    inference(avatar_split_clause,[],[f147,f124,f171])).
% 5.90/1.17  fof(f136,plain,(
% 5.90/1.17    ~spl12_3 | ~spl12_4),
% 5.90/1.17    inference(avatar_split_clause,[],[f81,f133,f129])).
% 5.90/1.17  fof(f81,plain,(
% 5.90/1.17    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.90/1.17    inference(definition_unfolding,[],[f28,f79,f79])).
% 5.90/1.17  fof(f28,plain,(
% 5.90/1.17    k1_tarski(sK0) != k1_relat_1(sK2) | k1_tarski(sK1) != k2_relat_1(sK2)),
% 5.90/1.17    inference(cnf_transformation,[],[f24])).
% 5.90/1.17  fof(f24,plain,(
% 5.90/1.17    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 5.90/1.17    inference(flattening,[],[f23])).
% 5.90/1.17  fof(f23,plain,(
% 5.90/1.17    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 5.90/1.17    inference(ennf_transformation,[],[f22])).
% 5.90/1.17  fof(f22,negated_conjecture,(
% 5.90/1.17    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 5.90/1.17    inference(negated_conjecture,[],[f21])).
% 5.90/1.17  fof(f21,conjecture,(
% 5.90/1.17    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 5.90/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 5.90/1.17  fof(f127,plain,(
% 5.90/1.17    spl12_2),
% 5.90/1.17    inference(avatar_split_clause,[],[f80,f124])).
% 5.90/1.17  fof(f80,plain,(
% 5.90/1.17    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 5.90/1.17    inference(definition_unfolding,[],[f30,f79])).
% 5.90/1.17  fof(f30,plain,(
% 5.90/1.17    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 5.90/1.17    inference(cnf_transformation,[],[f24])).
% 5.90/1.17  fof(f122,plain,(
% 5.90/1.17    spl12_1),
% 5.90/1.17    inference(avatar_split_clause,[],[f29,f119])).
% 5.90/1.17  fof(f29,plain,(
% 5.90/1.17    v1_relat_1(sK2)),
% 5.90/1.17    inference(cnf_transformation,[],[f24])).
% 5.90/1.17  % SZS output end Proof for theBenchmark
% 5.90/1.17  % (23044)------------------------------
% 5.90/1.17  % (23044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.90/1.17  % (23044)Termination reason: Refutation
% 5.90/1.17  
% 5.90/1.17  % (23044)Memory used [KB]: 13816
% 5.90/1.17  % (23044)Time elapsed: 0.650 s
% 5.90/1.17  % (23044)------------------------------
% 5.90/1.17  % (23044)------------------------------
% 5.90/1.17  % (23014)Success in time 0.821 s
%------------------------------------------------------------------------------
