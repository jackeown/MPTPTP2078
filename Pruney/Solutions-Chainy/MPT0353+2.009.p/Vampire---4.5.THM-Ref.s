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
% DateTime   : Thu Dec  3 12:44:21 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 205 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :    8
%              Number of atoms          :  295 ( 522 expanded)
%              Number of equality atoms :   74 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4925)Termination reason: Refutation not found, incomplete strategy

% (4925)Memory used [KB]: 10618
% (4925)Time elapsed: 0.150 s
% (4925)------------------------------
% (4925)------------------------------
fof(f827,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f94,f96,f120,f133,f145,f151,f161,f177,f197,f227,f233,f576,f600,f752,f826])).

fof(f826,plain,
    ( spl4_69
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f804,f224,f173,f749])).

fof(f749,plain,
    ( spl4_69
  <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f173,plain,
    ( spl4_13
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f224,plain,
    ( spl4_18
  <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f804,plain,
    ( k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(superposition,[],[f201,f226])).

fof(f226,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f201,plain,
    ( ! [X1] : k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k6_subset_1(sK0,X1))
    | ~ spl4_13 ),
    inference(superposition,[],[f54,f175])).

fof(f175,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f173])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k6_subset_1(X1,X2)) = k6_subset_1(k3_xboole_0(X0,X1),X2) ),
    inference(definition_unfolding,[],[f48,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f752,plain,
    ( ~ spl4_69
    | ~ spl4_10
    | ~ spl4_50
    | spl4_53 ),
    inference(avatar_split_clause,[],[f747,f597,f573,f148,f749])).

fof(f148,plain,
    ( spl4_10
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f573,plain,
    ( spl4_50
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f597,plain,
    ( spl4_53
  <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f747,plain,
    ( k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl4_10
    | ~ spl4_50
    | spl4_53 ),
    inference(superposition,[],[f599,f589])).

fof(f589,plain,
    ( ! [X0] : k3_xboole_0(X0,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2))
    | ~ spl4_10
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f245,f575])).

fof(f575,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f573])).

fof(f245,plain,
    ( ! [X0] : k3_xboole_0(X0,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f150,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f150,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f599,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f597])).

fof(f600,plain,
    ( ~ spl4_53
    | spl4_19
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f588,f573,f230,f597])).

fof(f230,plain,
    ( spl4_19
  <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f588,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_19
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f232,f575])).

fof(f232,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f230])).

fof(f576,plain,
    ( spl4_50
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f567,f224,f90,f573])).

fof(f90,plain,
    ( spl4_5
  <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f567,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f92,f226])).

fof(f92,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f233,plain,
    ( ~ spl4_19
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f228,f69,f59,f230])).

fof(f59,plain,
    ( spl4_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f228,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f61,f98])).

fof(f98,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f71,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f61,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f227,plain,
    ( spl4_18
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f222,f186,f224])).

fof(f186,plain,
    ( spl4_14
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f222,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f52,f188])).

fof(f188,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f197,plain,
    ( spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f184,f157,f186])).

fof(f157,plain,
    ( spl4_11
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f184,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f36,f159])).

fof(f159,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f177,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f171,f141,f173])).

fof(f141,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f171,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f143,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f143,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f161,plain,
    ( spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f155,f129,f157])).

fof(f129,plain,
    ( spl4_8
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f155,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f131,f42])).

fof(f131,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f151,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f146,f90,f148])).

fof(f146,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f34,f92])).

fof(f34,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f145,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f136,f109,f141])).

fof(f109,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f136,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f111,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f133,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f124,f85,f129])).

fof(f85,plain,
    ( spl4_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f124,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f87,f57])).

fof(f87,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f120,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f119,f69,f109])).

fof(f119,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f104,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f104,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f96,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f95,f64,f85])).

fof(f64,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f80,f33])).

fof(f80,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f94,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f79,f64,f90])).

fof(f79,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

% (4927)Termination reason: Refutation not found, incomplete strategy

% (4927)Memory used [KB]: 10618
% (4927)Time elapsed: 0.140 s
% (4927)------------------------------
% (4927)------------------------------
fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4929)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (4928)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (4945)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (4920)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4944)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (4917)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (4937)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (4926)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (4938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (4918)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (4930)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (4937)Refutation not found, incomplete strategy% (4937)------------------------------
% 0.20/0.52  % (4937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4937)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4937)Memory used [KB]: 1663
% 0.20/0.52  % (4937)Time elapsed: 0.110 s
% 0.20/0.52  % (4937)------------------------------
% 0.20/0.52  % (4937)------------------------------
% 0.20/0.52  % (4941)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (4920)Refutation not found, incomplete strategy% (4920)------------------------------
% 0.20/0.53  % (4920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4920)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4920)Memory used [KB]: 6140
% 0.20/0.53  % (4920)Time elapsed: 0.099 s
% 0.20/0.53  % (4920)------------------------------
% 0.20/0.53  % (4920)------------------------------
% 0.20/0.53  % (4943)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.53  % (4916)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (4936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.53  % (4933)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.53  % (4916)Refutation not found, incomplete strategy% (4916)------------------------------
% 1.34/0.53  % (4916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4916)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (4916)Memory used [KB]: 1663
% 1.34/0.53  % (4916)Time elapsed: 0.124 s
% 1.34/0.53  % (4916)------------------------------
% 1.34/0.53  % (4916)------------------------------
% 1.34/0.53  % (4919)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (4933)Refutation not found, incomplete strategy% (4933)------------------------------
% 1.34/0.53  % (4933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4933)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (4933)Memory used [KB]: 10618
% 1.34/0.53  % (4933)Time elapsed: 0.131 s
% 1.34/0.53  % (4933)------------------------------
% 1.34/0.53  % (4933)------------------------------
% 1.34/0.53  % (4921)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.53  % (4923)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.53  % (4936)Refutation not found, incomplete strategy% (4936)------------------------------
% 1.34/0.53  % (4936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4926)Refutation not found, incomplete strategy% (4926)------------------------------
% 1.34/0.53  % (4926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4926)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (4926)Memory used [KB]: 10618
% 1.34/0.53  % (4926)Time elapsed: 0.133 s
% 1.34/0.53  % (4926)------------------------------
% 1.34/0.53  % (4926)------------------------------
% 1.34/0.53  % (4922)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.54  % (4934)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (4936)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (4936)Memory used [KB]: 10746
% 1.34/0.54  % (4936)Time elapsed: 0.128 s
% 1.34/0.54  % (4936)------------------------------
% 1.34/0.54  % (4936)------------------------------
% 1.34/0.54  % (4938)Refutation not found, incomplete strategy% (4938)------------------------------
% 1.34/0.54  % (4938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (4938)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (4938)Memory used [KB]: 10746
% 1.34/0.54  % (4938)Time elapsed: 0.105 s
% 1.34/0.54  % (4938)------------------------------
% 1.34/0.54  % (4938)------------------------------
% 1.34/0.54  % (4932)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % (4935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (4927)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (4924)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % (4927)Refutation not found, incomplete strategy% (4927)------------------------------
% 1.34/0.54  % (4927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (4925)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.54  % (4940)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (4941)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.51/0.55  % (4931)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.55  % (4942)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.55  % (4939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.55  % (4925)Refutation not found, incomplete strategy% (4925)------------------------------
% 1.51/0.55  % (4925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (4931)Refutation not found, incomplete strategy% (4931)------------------------------
% 1.51/0.56  % (4931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (4931)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (4931)Memory used [KB]: 6140
% 1.51/0.56  % (4931)Time elapsed: 0.003 s
% 1.51/0.56  % (4931)------------------------------
% 1.51/0.56  % (4931)------------------------------
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  % (4925)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (4925)Memory used [KB]: 10618
% 1.51/0.56  % (4925)Time elapsed: 0.150 s
% 1.51/0.56  % (4925)------------------------------
% 1.51/0.56  % (4925)------------------------------
% 1.51/0.56  fof(f827,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f62,f67,f72,f94,f96,f120,f133,f145,f151,f161,f177,f197,f227,f233,f576,f600,f752,f826])).
% 1.51/0.56  fof(f826,plain,(
% 1.51/0.56    spl4_69 | ~spl4_13 | ~spl4_18),
% 1.51/0.56    inference(avatar_split_clause,[],[f804,f224,f173,f749])).
% 1.51/0.56  fof(f749,plain,(
% 1.51/0.56    spl4_69 <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.51/0.56  fof(f173,plain,(
% 1.51/0.56    spl4_13 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.51/0.56  fof(f224,plain,(
% 1.51/0.56    spl4_18 <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.51/0.56  fof(f804,plain,(
% 1.51/0.56    k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl4_13 | ~spl4_18)),
% 1.51/0.56    inference(superposition,[],[f201,f226])).
% 1.51/0.56  fof(f226,plain,(
% 1.51/0.56    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_18),
% 1.51/0.56    inference(avatar_component_clause,[],[f224])).
% 1.51/0.56  fof(f201,plain,(
% 1.51/0.56    ( ! [X1] : (k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k6_subset_1(sK0,X1))) ) | ~spl4_13),
% 1.51/0.56    inference(superposition,[],[f54,f175])).
% 1.51/0.56  fof(f175,plain,(
% 1.51/0.56    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_13),
% 1.51/0.56    inference(avatar_component_clause,[],[f173])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k6_subset_1(X1,X2)) = k6_subset_1(k3_xboole_0(X0,X1),X2)) )),
% 1.51/0.56    inference(definition_unfolding,[],[f48,f35,f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.51/0.56  fof(f48,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.51/0.56  fof(f752,plain,(
% 1.51/0.56    ~spl4_69 | ~spl4_10 | ~spl4_50 | spl4_53),
% 1.51/0.56    inference(avatar_split_clause,[],[f747,f597,f573,f148,f749])).
% 1.51/0.56  fof(f148,plain,(
% 1.51/0.56    spl4_10 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.51/0.56  fof(f573,plain,(
% 1.51/0.56    spl4_50 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.51/0.56  fof(f597,plain,(
% 1.51/0.56    spl4_53 <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.51/0.56  fof(f747,plain,(
% 1.51/0.56    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl4_10 | ~spl4_50 | spl4_53)),
% 1.51/0.56    inference(superposition,[],[f599,f589])).
% 1.51/0.56  fof(f589,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2))) ) | (~spl4_10 | ~spl4_50)),
% 1.51/0.56    inference(backward_demodulation,[],[f245,f575])).
% 1.51/0.56  fof(f575,plain,(
% 1.51/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_50),
% 1.51/0.56    inference(avatar_component_clause,[],[f573])).
% 1.51/0.56  fof(f245,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(X0,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2))) ) | ~spl4_10),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f150,f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.51/0.56  fof(f150,plain,(
% 1.51/0.56    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_10),
% 1.51/0.56    inference(avatar_component_clause,[],[f148])).
% 1.51/0.56  fof(f599,plain,(
% 1.51/0.56    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | spl4_53),
% 1.51/0.56    inference(avatar_component_clause,[],[f597])).
% 1.51/0.56  fof(f600,plain,(
% 1.51/0.56    ~spl4_53 | spl4_19 | ~spl4_50),
% 1.51/0.56    inference(avatar_split_clause,[],[f588,f573,f230,f597])).
% 1.51/0.56  fof(f230,plain,(
% 1.51/0.56    spl4_19 <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.51/0.56  fof(f588,plain,(
% 1.51/0.56    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | (spl4_19 | ~spl4_50)),
% 1.51/0.56    inference(backward_demodulation,[],[f232,f575])).
% 1.51/0.56  fof(f232,plain,(
% 1.51/0.56    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | spl4_19),
% 1.51/0.56    inference(avatar_component_clause,[],[f230])).
% 1.51/0.56  fof(f576,plain,(
% 1.51/0.56    spl4_50 | ~spl4_5 | ~spl4_18),
% 1.51/0.56    inference(avatar_split_clause,[],[f567,f224,f90,f573])).
% 1.51/0.56  fof(f90,plain,(
% 1.51/0.56    spl4_5 <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.51/0.56  fof(f567,plain,(
% 1.51/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl4_5 | ~spl4_18)),
% 1.51/0.56    inference(backward_demodulation,[],[f92,f226])).
% 1.51/0.56  fof(f92,plain,(
% 1.51/0.56    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_5),
% 1.51/0.56    inference(avatar_component_clause,[],[f90])).
% 1.51/0.56  fof(f233,plain,(
% 1.51/0.56    ~spl4_19 | spl4_1 | ~spl4_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f228,f69,f59,f230])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    spl4_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.51/0.56  fof(f228,plain,(
% 1.51/0.56    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | (spl4_1 | ~spl4_3)),
% 1.51/0.56    inference(backward_demodulation,[],[f61,f98])).
% 1.51/0.56  fof(f98,plain,(
% 1.51/0.56    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)) ) | ~spl4_3),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f71,f55])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f50,f35])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.51/0.56  fof(f71,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.51/0.56    inference(avatar_component_clause,[],[f69])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl4_1),
% 1.51/0.56    inference(avatar_component_clause,[],[f59])).
% 1.51/0.56  fof(f227,plain,(
% 1.51/0.56    spl4_18 | ~spl4_14),
% 1.51/0.56    inference(avatar_split_clause,[],[f222,f186,f224])).
% 1.51/0.56  fof(f186,plain,(
% 1.51/0.56    spl4_14 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.51/0.56  fof(f222,plain,(
% 1.51/0.56    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_14),
% 1.51/0.56    inference(superposition,[],[f52,f188])).
% 1.51/0.56  fof(f188,plain,(
% 1.51/0.56    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_14),
% 1.51/0.56    inference(avatar_component_clause,[],[f186])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 1.51/0.56    inference(definition_unfolding,[],[f37,f35])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.56  fof(f197,plain,(
% 1.51/0.56    spl4_14 | ~spl4_11),
% 1.51/0.56    inference(avatar_split_clause,[],[f184,f157,f186])).
% 1.51/0.56  fof(f157,plain,(
% 1.51/0.56    spl4_11 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.51/0.56  fof(f184,plain,(
% 1.51/0.56    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_11),
% 1.51/0.56    inference(superposition,[],[f36,f159])).
% 1.51/0.56  fof(f159,plain,(
% 1.51/0.56    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_11),
% 1.51/0.56    inference(avatar_component_clause,[],[f157])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.51/0.56  fof(f177,plain,(
% 1.51/0.56    spl4_13 | ~spl4_9),
% 1.51/0.56    inference(avatar_split_clause,[],[f171,f141,f173])).
% 1.51/0.56  fof(f141,plain,(
% 1.51/0.56    spl4_9 <=> r1_tarski(sK1,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.51/0.56  fof(f171,plain,(
% 1.51/0.56    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_9),
% 1.51/0.56    inference(resolution,[],[f143,f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.51/0.56  fof(f143,plain,(
% 1.51/0.56    r1_tarski(sK1,sK0) | ~spl4_9),
% 1.51/0.56    inference(avatar_component_clause,[],[f141])).
% 1.51/0.56  fof(f161,plain,(
% 1.51/0.56    spl4_11 | ~spl4_8),
% 1.51/0.56    inference(avatar_split_clause,[],[f155,f129,f157])).
% 1.51/0.56  fof(f129,plain,(
% 1.51/0.56    spl4_8 <=> r1_tarski(sK2,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.51/0.56  fof(f155,plain,(
% 1.51/0.56    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_8),
% 1.51/0.56    inference(resolution,[],[f131,f42])).
% 1.51/0.56  fof(f131,plain,(
% 1.51/0.56    r1_tarski(sK2,sK0) | ~spl4_8),
% 1.51/0.56    inference(avatar_component_clause,[],[f129])).
% 1.51/0.56  fof(f151,plain,(
% 1.51/0.56    spl4_10 | ~spl4_5),
% 1.51/0.56    inference(avatar_split_clause,[],[f146,f90,f148])).
% 1.51/0.56  fof(f146,plain,(
% 1.51/0.56    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_5),
% 1.51/0.56    inference(superposition,[],[f34,f92])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.51/0.56  fof(f145,plain,(
% 1.51/0.56    spl4_9 | ~spl4_6),
% 1.51/0.56    inference(avatar_split_clause,[],[f136,f109,f141])).
% 1.51/0.56  fof(f109,plain,(
% 1.51/0.56    spl4_6 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.51/0.56  fof(f136,plain,(
% 1.51/0.56    r1_tarski(sK1,sK0) | ~spl4_6),
% 1.51/0.56    inference(resolution,[],[f111,f57])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(equality_resolution,[],[f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(rectify,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.51/0.56  fof(f111,plain,(
% 1.51/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_6),
% 1.51/0.56    inference(avatar_component_clause,[],[f109])).
% 1.51/0.56  fof(f133,plain,(
% 1.51/0.56    spl4_8 | ~spl4_4),
% 1.51/0.56    inference(avatar_split_clause,[],[f124,f85,f129])).
% 1.51/0.56  fof(f85,plain,(
% 1.51/0.56    spl4_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    r1_tarski(sK2,sK0) | ~spl4_4),
% 1.51/0.56    inference(resolution,[],[f87,f57])).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_4),
% 1.51/0.56    inference(avatar_component_clause,[],[f85])).
% 1.51/0.56  fof(f120,plain,(
% 1.51/0.56    spl4_6 | ~spl4_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f119,f69,f109])).
% 1.51/0.56  fof(f119,plain,(
% 1.51/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.51/0.56    inference(subsumption_resolution,[],[f104,f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.51/0.56  fof(f104,plain,(
% 1.51/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.51/0.56    inference(resolution,[],[f71,f38])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.51/0.56    inference(nnf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.51/0.56  fof(f96,plain,(
% 1.51/0.56    spl4_4 | ~spl4_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f95,f64,f85])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.51/0.56  fof(f95,plain,(
% 1.51/0.56    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.51/0.56    inference(subsumption_resolution,[],[f80,f33])).
% 1.51/0.56  fof(f80,plain,(
% 1.51/0.56    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.51/0.56    inference(resolution,[],[f66,f38])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f64])).
% 1.51/0.56  fof(f94,plain,(
% 1.51/0.56    spl4_5 | ~spl4_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f79,f64,f90])).
% 1.51/0.56  fof(f79,plain,(
% 1.51/0.56    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_2),
% 1.51/0.56    inference(resolution,[],[f66,f53])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f43,f35])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    spl4_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f30,f69])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23,f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f15])).
% 1.51/0.56  % (4927)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (4927)Memory used [KB]: 10618
% 1.51/0.56  % (4927)Time elapsed: 0.140 s
% 1.51/0.56  % (4927)------------------------------
% 1.51/0.56  % (4927)------------------------------
% 1.51/0.56  fof(f15,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.51/0.56    inference(negated_conjecture,[],[f14])).
% 1.51/0.56  fof(f14,conjecture,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    spl4_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f31,f64])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    ~spl4_1),
% 1.51/0.56    inference(avatar_split_clause,[],[f32,f59])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (4941)------------------------------
% 1.51/0.56  % (4941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (4941)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (4941)Memory used [KB]: 6780
% 1.51/0.56  % (4941)Time elapsed: 0.132 s
% 1.51/0.56  % (4941)------------------------------
% 1.51/0.56  % (4941)------------------------------
% 1.51/0.56  % (4915)Success in time 0.205 s
%------------------------------------------------------------------------------
