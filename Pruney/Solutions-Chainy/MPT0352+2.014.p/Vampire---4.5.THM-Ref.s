%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 287 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :   11
%              Number of atoms          :  417 ( 824 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f82,f87,f115,f117,f135,f137,f197,f227,f228,f240,f265,f475,f510,f552,f576,f577,f591,f766,f934,f1119,f1121,f1146,f1155])).

fof(f1155,plain,
    ( spl4_24
    | ~ spl4_30
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | spl4_24
    | ~ spl4_30
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1153,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1153,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | spl4_24
    | ~ spl4_30
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f1152,f762])).

fof(f762,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl4_45
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1152,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1))
    | spl4_24
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1151,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1151,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0))
    | spl4_24
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1150,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1150,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | spl4_24
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1139,f44])).

fof(f1139,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | spl4_24
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f357,f508,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f508,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl4_30
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f357,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl4_24
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1146,plain,
    ( spl4_31
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f1143,f506,f530])).

fof(f530,plain,
    ( spl4_31
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1143,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f508,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1121,plain,
    ( spl4_30
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f542,f530,f506])).

fof(f542,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f532,f52])).

fof(f532,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f530])).

fof(f1119,plain,
    ( ~ spl4_1
    | spl4_31
    | ~ spl4_55 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | ~ spl4_1
    | spl4_31
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f1109,f70])).

fof(f70,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1109,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_31
    | ~ spl4_55 ),
    inference(superposition,[],[f734,f930])).

fof(f930,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f928])).

fof(f928,plain,
    ( spl4_55
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f734,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))
    | spl4_31 ),
    inference(unit_resulting_resolution,[],[f531,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f531,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f530])).

fof(f934,plain,
    ( spl4_55
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f920,f218,f928])).

fof(f218,plain,
    ( spl4_15
  <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f920,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_15 ),
    inference(superposition,[],[f64,f220])).

fof(f220,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f766,plain,
    ( spl4_45
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f758,f261,f760])).

fof(f261,plain,
    ( spl4_19
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f758,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl4_19 ),
    inference(superposition,[],[f44,f263])).

fof(f263,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f261])).

fof(f591,plain,
    ( ~ spl4_24
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f590,f131,f111,f73,f356])).

fof(f73,plain,
    ( spl4_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f111,plain,
    ( spl4_7
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f131,plain,
    ( spl4_9
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f590,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f589,f113])).

fof(f113,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f589,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f75,f133])).

fof(f133,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f75,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f577,plain,
    ( sK0 != k2_xboole_0(sK0,sK2)
    | r1_tarski(sK1,k2_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f576,plain,
    ( spl4_34
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f568,f223,f570])).

fof(f570,plain,
    ( spl4_34
  <=> sK0 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f223,plain,
    ( spl4_16
  <=> sK0 = k2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f568,plain,
    ( sK0 = k2_xboole_0(sK0,sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f44,f225])).

fof(f225,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f552,plain,
    ( ~ spl4_32
    | spl4_1
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f547,f530,f69,f549])).

fof(f549,plain,
    ( spl4_32
  <=> r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f547,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK2))
    | spl4_1
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f546,f44])).

fof(f546,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,sK0))
    | spl4_1
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f540,f46])).

fof(f540,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2)))
    | spl4_1
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f71,f532,f62])).

fof(f71,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f510,plain,
    ( spl4_30
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f498,f356,f506])).

fof(f498,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_24 ),
    inference(resolution,[],[f358,f61])).

fof(f358,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f356])).

fof(f475,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f474,f131,f111,f73,f356])).

fof(f474,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f473,f113])).

fof(f473,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f74,f133])).

fof(f74,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f265,plain,
    ( spl4_19
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f253,f236,f261])).

fof(f236,plain,
    ( spl4_17
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f253,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f238,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f238,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f236])).

fof(f240,plain,
    ( spl4_17
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f231,f126,f236])).

fof(f126,plain,
    ( spl4_8
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f231,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f128,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f128,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f228,plain,
    ( spl4_15
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f216,f193,f218])).

fof(f193,plain,
    ( spl4_14
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f216,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f195,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f195,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f227,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f215,f193,f223])).

fof(f215,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f195,f54])).

fof(f197,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f188,f106,f193])).

fof(f106,plain,
    ( spl4_6
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f188,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f108,f67])).

fof(f108,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f137,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f136,f84,f126])).

fof(f84,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f136,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f121,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f135,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f120,f84,f131])).

fof(f120,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f117,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f116,f79,f106])).

fof(f79,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f81,f48])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f115,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f79,f111])).

fof(f100,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f81,f55])).

fof(f87,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f39,f73,f69])).

fof(f39,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f73,f69])).

fof(f40,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (16710)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (16719)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (16702)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (16719)Refutation not found, incomplete strategy% (16719)------------------------------
% 0.22/0.52  % (16719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16719)Memory used [KB]: 10746
% 0.22/0.52  % (16719)Time elapsed: 0.112 s
% 0.22/0.52  % (16711)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (16719)------------------------------
% 0.22/0.52  % (16719)------------------------------
% 0.22/0.53  % (16704)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (16720)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (16712)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (16699)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (16698)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (16721)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (16701)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (16697)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (16703)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (16697)Refutation not found, incomplete strategy% (16697)------------------------------
% 0.22/0.54  % (16697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16697)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16697)Memory used [KB]: 1663
% 0.22/0.54  % (16697)Time elapsed: 0.123 s
% 0.22/0.54  % (16697)------------------------------
% 0.22/0.54  % (16697)------------------------------
% 0.22/0.55  % (16713)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (16700)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (16722)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (16708)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (16723)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (16705)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (16714)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (16726)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (16714)Refutation not found, incomplete strategy% (16714)------------------------------
% 0.22/0.55  % (16714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16714)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16714)Memory used [KB]: 10618
% 0.22/0.55  % (16714)Time elapsed: 0.138 s
% 0.22/0.55  % (16714)------------------------------
% 0.22/0.55  % (16714)------------------------------
% 0.22/0.55  % (16715)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (16724)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (16707)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (16707)Refutation not found, incomplete strategy% (16707)------------------------------
% 0.22/0.56  % (16707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16707)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (16707)Memory used [KB]: 10618
% 0.22/0.56  % (16707)Time elapsed: 0.149 s
% 0.22/0.56  % (16707)------------------------------
% 0.22/0.56  % (16707)------------------------------
% 0.22/0.56  % (16718)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (16716)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (16709)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (16708)Refutation not found, incomplete strategy% (16708)------------------------------
% 0.22/0.57  % (16708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16708)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (16708)Memory used [KB]: 10618
% 0.22/0.57  % (16708)Time elapsed: 0.159 s
% 0.22/0.57  % (16708)------------------------------
% 0.22/0.57  % (16708)------------------------------
% 0.22/0.58  % (16725)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.59  % (16717)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (16722)Refutation found. Thanks to Tanya!
% 0.22/0.60  % SZS status Theorem for theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f1156,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(avatar_sat_refutation,[],[f76,f77,f82,f87,f115,f117,f135,f137,f197,f227,f228,f240,f265,f475,f510,f552,f576,f577,f591,f766,f934,f1119,f1121,f1146,f1155])).
% 0.22/0.60  fof(f1155,plain,(
% 0.22/0.60    spl4_24 | ~spl4_30 | ~spl4_45),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f1154])).
% 0.22/0.60  fof(f1154,plain,(
% 0.22/0.60    $false | (spl4_24 | ~spl4_30 | ~spl4_45)),
% 0.22/0.60    inference(subsumption_resolution,[],[f1153,f42])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.60  fof(f1153,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | (spl4_24 | ~spl4_30 | ~spl4_45)),
% 0.22/0.60    inference(forward_demodulation,[],[f1152,f762])).
% 0.22/0.60  fof(f762,plain,(
% 0.22/0.60    sK0 = k2_xboole_0(sK0,sK1) | ~spl4_45),
% 0.22/0.60    inference(avatar_component_clause,[],[f760])).
% 0.22/0.60  fof(f760,plain,(
% 0.22/0.60    spl4_45 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.60  fof(f1152,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1)) | (spl4_24 | ~spl4_30)),
% 0.22/0.60    inference(forward_demodulation,[],[f1151,f44])).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.60  fof(f1151,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) | (spl4_24 | ~spl4_30)),
% 0.22/0.60    inference(forward_demodulation,[],[f1150,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.60  fof(f1150,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | (spl4_24 | ~spl4_30)),
% 0.22/0.60    inference(forward_demodulation,[],[f1139,f44])).
% 0.22/0.60  fof(f1139,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | (spl4_24 | ~spl4_30)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f357,f508,f62])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.60    inference(flattening,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.60    inference(ennf_transformation,[],[f11])).
% 0.22/0.60  fof(f11,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.22/0.60  fof(f508,plain,(
% 0.22/0.60    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_30),
% 0.22/0.60    inference(avatar_component_clause,[],[f506])).
% 0.22/0.60  fof(f506,plain,(
% 0.22/0.60    spl4_30 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.60  fof(f357,plain,(
% 0.22/0.60    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_24),
% 0.22/0.60    inference(avatar_component_clause,[],[f356])).
% 0.22/0.60  fof(f356,plain,(
% 0.22/0.60    spl4_24 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.60  fof(f1146,plain,(
% 0.22/0.60    spl4_31 | ~spl4_30),
% 0.22/0.60    inference(avatar_split_clause,[],[f1143,f506,f530])).
% 0.22/0.60  fof(f530,plain,(
% 0.22/0.60    spl4_31 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.60  fof(f1143,plain,(
% 0.22/0.60    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_30),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f508,f52])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.60  fof(f1121,plain,(
% 0.22/0.60    spl4_30 | ~spl4_31),
% 0.22/0.60    inference(avatar_split_clause,[],[f542,f530,f506])).
% 0.22/0.60  fof(f542,plain,(
% 0.22/0.60    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_31),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f532,f52])).
% 0.22/0.60  fof(f532,plain,(
% 0.22/0.60    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_31),
% 0.22/0.60    inference(avatar_component_clause,[],[f530])).
% 0.22/0.60  fof(f1119,plain,(
% 0.22/0.60    ~spl4_1 | spl4_31 | ~spl4_55),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f1118])).
% 0.22/0.60  fof(f1118,plain,(
% 0.22/0.60    $false | (~spl4_1 | spl4_31 | ~spl4_55)),
% 0.22/0.60    inference(subsumption_resolution,[],[f1109,f70])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f69])).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.60  fof(f1109,plain,(
% 0.22/0.60    ~r1_tarski(sK1,sK2) | (spl4_31 | ~spl4_55)),
% 0.22/0.60    inference(superposition,[],[f734,f930])).
% 0.22/0.60  fof(f930,plain,(
% 0.22/0.60    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_55),
% 0.22/0.60    inference(avatar_component_clause,[],[f928])).
% 0.22/0.60  fof(f928,plain,(
% 0.22/0.60    spl4_55 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.22/0.60  fof(f734,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) ) | spl4_31),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f531,f61])).
% 0.22/0.60  fof(f61,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.60  fof(f531,plain,(
% 0.22/0.60    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl4_31),
% 0.22/0.60    inference(avatar_component_clause,[],[f530])).
% 0.22/0.60  fof(f934,plain,(
% 0.22/0.60    spl4_55 | ~spl4_15),
% 0.22/0.60    inference(avatar_split_clause,[],[f920,f218,f928])).
% 0.22/0.60  fof(f218,plain,(
% 0.22/0.60    spl4_15 <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.60  fof(f920,plain,(
% 0.22/0.60    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_15),
% 0.22/0.60    inference(superposition,[],[f64,f220])).
% 0.22/0.60  fof(f220,plain,(
% 0.22/0.60    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_15),
% 0.22/0.60    inference(avatar_component_clause,[],[f218])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f43,f45,f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.60  fof(f766,plain,(
% 0.22/0.60    spl4_45 | ~spl4_19),
% 0.22/0.60    inference(avatar_split_clause,[],[f758,f261,f760])).
% 0.22/0.60  fof(f261,plain,(
% 0.22/0.60    spl4_19 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.60  fof(f758,plain,(
% 0.22/0.60    sK0 = k2_xboole_0(sK0,sK1) | ~spl4_19),
% 0.22/0.60    inference(superposition,[],[f44,f263])).
% 0.22/0.61  fof(f263,plain,(
% 0.22/0.61    sK0 = k2_xboole_0(sK1,sK0) | ~spl4_19),
% 0.22/0.61    inference(avatar_component_clause,[],[f261])).
% 0.22/0.61  fof(f591,plain,(
% 0.22/0.61    ~spl4_24 | spl4_2 | ~spl4_7 | ~spl4_9),
% 0.22/0.61    inference(avatar_split_clause,[],[f590,f131,f111,f73,f356])).
% 0.22/0.61  fof(f73,plain,(
% 0.22/0.61    spl4_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.61  fof(f111,plain,(
% 0.22/0.61    spl4_7 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.61  fof(f131,plain,(
% 0.22/0.61    spl4_9 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.61  fof(f590,plain,(
% 0.22/0.61    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl4_2 | ~spl4_7 | ~spl4_9)),
% 0.22/0.61    inference(forward_demodulation,[],[f589,f113])).
% 0.22/0.61  fof(f113,plain,(
% 0.22/0.61    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_7),
% 0.22/0.61    inference(avatar_component_clause,[],[f111])).
% 0.22/0.61  fof(f589,plain,(
% 0.22/0.61    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl4_2 | ~spl4_9)),
% 0.22/0.61    inference(forward_demodulation,[],[f75,f133])).
% 0.22/0.61  fof(f133,plain,(
% 0.22/0.61    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_9),
% 0.22/0.61    inference(avatar_component_clause,[],[f131])).
% 0.22/0.61  fof(f75,plain,(
% 0.22/0.61    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_2),
% 0.22/0.61    inference(avatar_component_clause,[],[f73])).
% 0.22/0.61  fof(f577,plain,(
% 0.22/0.61    sK0 != k2_xboole_0(sK0,sK2) | r1_tarski(sK1,k2_xboole_0(sK0,sK2)) | ~r1_tarski(sK1,sK0)),
% 0.22/0.61    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.61  fof(f576,plain,(
% 0.22/0.61    spl4_34 | ~spl4_16),
% 0.22/0.61    inference(avatar_split_clause,[],[f568,f223,f570])).
% 0.22/0.61  fof(f570,plain,(
% 0.22/0.61    spl4_34 <=> sK0 = k2_xboole_0(sK0,sK2)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.61  fof(f223,plain,(
% 0.22/0.61    spl4_16 <=> sK0 = k2_xboole_0(sK2,sK0)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.61  fof(f568,plain,(
% 0.22/0.61    sK0 = k2_xboole_0(sK0,sK2) | ~spl4_16),
% 0.22/0.61    inference(superposition,[],[f44,f225])).
% 0.22/0.61  fof(f225,plain,(
% 0.22/0.61    sK0 = k2_xboole_0(sK2,sK0) | ~spl4_16),
% 0.22/0.61    inference(avatar_component_clause,[],[f223])).
% 0.22/0.61  fof(f552,plain,(
% 0.22/0.61    ~spl4_32 | spl4_1 | ~spl4_31),
% 0.22/0.61    inference(avatar_split_clause,[],[f547,f530,f69,f549])).
% 0.22/0.61  fof(f549,plain,(
% 0.22/0.61    spl4_32 <=> r1_tarski(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.61  fof(f547,plain,(
% 0.22/0.61    ~r1_tarski(sK1,k2_xboole_0(sK0,sK2)) | (spl4_1 | ~spl4_31)),
% 0.22/0.61    inference(forward_demodulation,[],[f546,f44])).
% 0.22/0.61  fof(f546,plain,(
% 0.22/0.61    ~r1_tarski(sK1,k2_xboole_0(sK2,sK0)) | (spl4_1 | ~spl4_31)),
% 0.22/0.61    inference(forward_demodulation,[],[f540,f46])).
% 0.22/0.61  fof(f540,plain,(
% 0.22/0.61    ~r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))) | (spl4_1 | ~spl4_31)),
% 0.22/0.61    inference(unit_resulting_resolution,[],[f71,f532,f62])).
% 0.22/0.61  fof(f71,plain,(
% 0.22/0.61    ~r1_tarski(sK1,sK2) | spl4_1),
% 0.22/0.61    inference(avatar_component_clause,[],[f69])).
% 0.22/0.61  fof(f510,plain,(
% 0.22/0.61    spl4_30 | ~spl4_24),
% 0.22/0.61    inference(avatar_split_clause,[],[f498,f356,f506])).
% 0.22/0.61  fof(f498,plain,(
% 0.22/0.61    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_24),
% 0.22/0.61    inference(resolution,[],[f358,f61])).
% 0.22/0.61  fof(f358,plain,(
% 0.22/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_24),
% 0.22/0.61    inference(avatar_component_clause,[],[f356])).
% 0.22/0.61  fof(f475,plain,(
% 0.22/0.61    spl4_24 | ~spl4_2 | ~spl4_7 | ~spl4_9),
% 0.22/0.61    inference(avatar_split_clause,[],[f474,f131,f111,f73,f356])).
% 0.22/0.61  fof(f474,plain,(
% 0.22/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_2 | ~spl4_7 | ~spl4_9)),
% 0.22/0.61    inference(forward_demodulation,[],[f473,f113])).
% 0.22/0.61  fof(f473,plain,(
% 0.22/0.61    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_2 | ~spl4_9)),
% 0.22/0.61    inference(forward_demodulation,[],[f74,f133])).
% 0.22/0.61  fof(f74,plain,(
% 0.22/0.61    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_2),
% 0.22/0.61    inference(avatar_component_clause,[],[f73])).
% 0.22/0.61  fof(f265,plain,(
% 0.22/0.61    spl4_19 | ~spl4_17),
% 0.22/0.61    inference(avatar_split_clause,[],[f253,f236,f261])).
% 0.22/0.61  fof(f236,plain,(
% 0.22/0.61    spl4_17 <=> r1_tarski(sK1,sK0)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.61  fof(f253,plain,(
% 0.22/0.61    sK0 = k2_xboole_0(sK1,sK0) | ~spl4_17),
% 0.22/0.61    inference(resolution,[],[f238,f54])).
% 0.22/0.61  fof(f54,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f22])).
% 0.22/0.61  fof(f22,plain,(
% 0.22/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f6])).
% 0.22/0.61  fof(f6,axiom,(
% 0.22/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.61  fof(f238,plain,(
% 0.22/0.61    r1_tarski(sK1,sK0) | ~spl4_17),
% 0.22/0.61    inference(avatar_component_clause,[],[f236])).
% 0.22/0.61  fof(f240,plain,(
% 0.22/0.61    spl4_17 | ~spl4_8),
% 0.22/0.61    inference(avatar_split_clause,[],[f231,f126,f236])).
% 0.22/0.61  fof(f126,plain,(
% 0.22/0.61    spl4_8 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.61  fof(f231,plain,(
% 0.22/0.61    r1_tarski(sK1,sK0) | ~spl4_8),
% 0.22/0.61    inference(resolution,[],[f128,f67])).
% 0.22/0.61  fof(f67,plain,(
% 0.22/0.61    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.61    inference(equality_resolution,[],[f56])).
% 0.22/0.61  fof(f56,plain,(
% 0.22/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f36])).
% 0.22/0.61  fof(f36,plain,(
% 0.22/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f34,plain,(
% 0.22/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.61    inference(rectify,[],[f33])).
% 0.22/0.61  fof(f33,plain,(
% 0.22/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.61    inference(nnf_transformation,[],[f12])).
% 0.22/0.61  fof(f12,axiom,(
% 0.22/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.61  fof(f128,plain,(
% 0.22/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_8),
% 0.22/0.61    inference(avatar_component_clause,[],[f126])).
% 0.22/0.61  fof(f228,plain,(
% 0.22/0.61    spl4_15 | ~spl4_14),
% 0.22/0.61    inference(avatar_split_clause,[],[f216,f193,f218])).
% 0.22/0.61  fof(f193,plain,(
% 0.22/0.61    spl4_14 <=> r1_tarski(sK2,sK0)),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.61  fof(f216,plain,(
% 0.22/0.61    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_14),
% 0.22/0.61    inference(resolution,[],[f195,f65])).
% 0.22/0.61  fof(f65,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(definition_unfolding,[],[f53,f45])).
% 0.22/0.61  fof(f53,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f21])).
% 0.22/0.61  fof(f21,plain,(
% 0.22/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f7])).
% 0.22/0.61  fof(f7,axiom,(
% 0.22/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.61  fof(f195,plain,(
% 0.22/0.61    r1_tarski(sK2,sK0) | ~spl4_14),
% 0.22/0.61    inference(avatar_component_clause,[],[f193])).
% 0.22/0.61  fof(f227,plain,(
% 0.22/0.61    spl4_16 | ~spl4_14),
% 0.22/0.61    inference(avatar_split_clause,[],[f215,f193,f223])).
% 0.22/0.61  fof(f215,plain,(
% 0.22/0.61    sK0 = k2_xboole_0(sK2,sK0) | ~spl4_14),
% 0.22/0.61    inference(resolution,[],[f195,f54])).
% 0.22/0.61  fof(f197,plain,(
% 0.22/0.61    spl4_14 | ~spl4_6),
% 0.22/0.61    inference(avatar_split_clause,[],[f188,f106,f193])).
% 0.22/0.61  fof(f106,plain,(
% 0.22/0.61    spl4_6 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.61  fof(f188,plain,(
% 0.22/0.61    r1_tarski(sK2,sK0) | ~spl4_6),
% 0.22/0.61    inference(resolution,[],[f108,f67])).
% 0.22/0.61  fof(f108,plain,(
% 0.22/0.61    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.22/0.61    inference(avatar_component_clause,[],[f106])).
% 0.22/0.61  fof(f137,plain,(
% 0.22/0.61    spl4_8 | ~spl4_4),
% 0.22/0.61    inference(avatar_split_clause,[],[f136,f84,f126])).
% 0.22/0.61  fof(f84,plain,(
% 0.22/0.61    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.61  fof(f136,plain,(
% 0.22/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.61    inference(subsumption_resolution,[],[f121,f41])).
% 0.22/0.61  fof(f41,plain,(
% 0.22/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f15])).
% 0.22/0.61  fof(f15,axiom,(
% 0.22/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.61  fof(f121,plain,(
% 0.22/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.61    inference(resolution,[],[f86,f48])).
% 0.22/0.61  fof(f48,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.61    inference(nnf_transformation,[],[f19])).
% 0.22/0.61  fof(f19,plain,(
% 0.22/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f13])).
% 0.22/0.61  fof(f13,axiom,(
% 0.22/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.61  fof(f86,plain,(
% 0.22/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.61    inference(avatar_component_clause,[],[f84])).
% 0.22/0.61  fof(f135,plain,(
% 0.22/0.61    spl4_9 | ~spl4_4),
% 0.22/0.61    inference(avatar_split_clause,[],[f120,f84,f131])).
% 0.22/0.61  fof(f120,plain,(
% 0.22/0.61    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_4),
% 0.22/0.61    inference(resolution,[],[f86,f55])).
% 0.22/0.61  fof(f55,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f23])).
% 0.22/0.61  fof(f23,plain,(
% 0.22/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f14])).
% 0.22/0.61  fof(f14,axiom,(
% 0.22/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.61  fof(f117,plain,(
% 0.22/0.61    spl4_6 | ~spl4_3),
% 0.22/0.61    inference(avatar_split_clause,[],[f116,f79,f106])).
% 0.22/0.61  fof(f79,plain,(
% 0.22/0.61    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.61  fof(f116,plain,(
% 0.22/0.61    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.22/0.61    inference(subsumption_resolution,[],[f101,f41])).
% 0.22/0.61  fof(f101,plain,(
% 0.22/0.61    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.22/0.61    inference(resolution,[],[f81,f48])).
% 0.22/0.61  fof(f81,plain,(
% 0.22/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.22/0.61    inference(avatar_component_clause,[],[f79])).
% 0.22/0.61  fof(f115,plain,(
% 0.22/0.61    spl4_7 | ~spl4_3),
% 0.22/0.61    inference(avatar_split_clause,[],[f100,f79,f111])).
% 0.22/0.61  fof(f100,plain,(
% 0.22/0.61    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_3),
% 0.22/0.61    inference(resolution,[],[f81,f55])).
% 0.22/0.61  fof(f87,plain,(
% 0.22/0.61    spl4_4),
% 0.22/0.61    inference(avatar_split_clause,[],[f37,f84])).
% 0.22/0.61  fof(f37,plain,(
% 0.22/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f30,plain,(
% 0.22/0.61    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(flattening,[],[f27])).
% 0.22/0.61  fof(f27,plain,(
% 0.22/0.61    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(nnf_transformation,[],[f18])).
% 0.22/0.61  fof(f18,plain,(
% 0.22/0.61    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f17])).
% 0.22/0.61  fof(f17,negated_conjecture,(
% 0.22/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.61    inference(negated_conjecture,[],[f16])).
% 0.22/0.61  fof(f16,conjecture,(
% 0.22/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.22/0.61  fof(f82,plain,(
% 0.22/0.61    spl4_3),
% 0.22/0.61    inference(avatar_split_clause,[],[f38,f79])).
% 0.22/0.61  fof(f38,plain,(
% 0.22/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f77,plain,(
% 0.22/0.61    spl4_1 | spl4_2),
% 0.22/0.61    inference(avatar_split_clause,[],[f39,f73,f69])).
% 0.22/0.61  fof(f39,plain,(
% 0.22/0.61    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f76,plain,(
% 0.22/0.61    ~spl4_1 | ~spl4_2),
% 0.22/0.61    inference(avatar_split_clause,[],[f40,f73,f69])).
% 0.22/0.61  fof(f40,plain,(
% 0.22/0.61    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (16706)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.61  % (16722)------------------------------
% 0.22/0.61  % (16722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (16722)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (16722)Memory used [KB]: 6908
% 0.22/0.61  % (16722)Time elapsed: 0.176 s
% 0.22/0.61  % (16722)------------------------------
% 0.22/0.61  % (16722)------------------------------
% 0.22/0.61  % (16696)Success in time 0.245 s
%------------------------------------------------------------------------------
