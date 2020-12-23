%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:08 EST 2020

% Result     : Theorem 4.40s
% Output     : Refutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 763 expanded)
%              Number of leaves         :   67 ( 302 expanded)
%              Depth                    :   12
%              Number of atoms          :  681 (1733 expanded)
%              Number of equality atoms :  247 ( 806 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32735)Termination reason: Time limit

% (32735)Memory used [KB]: 8571
% (32735)Time elapsed: 0.424 s
% (32735)------------------------------
% (32735)------------------------------
fof(f4689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f86,f91,f98,f136,f145,f161,f439,f631,f1204,f1268,f1369,f1733,f1738,f1744,f1780,f1983,f2086,f2158,f2161,f2199,f2202,f2317,f2657,f2728,f2769,f2792,f2839,f2844,f2862,f2925,f3043,f3056,f3082,f3110,f3213,f3228,f3231,f3272,f3350,f3498,f3506,f3911,f3996,f4664,f4667,f4676,f4679,f4683,f4688])).

fof(f4688,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2)
    | k1_xboole_0 != sK1
    | sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | k1_tarski(sK0) != k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))
    | sK2 = k1_tarski(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4683,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4679,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_xboole_0,sK2)
    | sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | k1_tarski(sK0) != k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0))
    | k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2))
    | sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4676,plain,
    ( spl4_197
    | spl4_81
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f4671,f4661,f1985,f4673])).

fof(f4673,plain,
    ( spl4_197
  <=> k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f1985,plain,
    ( spl4_81
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f4661,plain,
    ( spl4_196
  <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f4671,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2)
    | spl4_81
    | ~ spl4_196 ),
    inference(subsumption_resolution,[],[f4668,f1987])).

fof(f1987,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2)
    | spl4_81 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f4668,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_196 ),
    inference(resolution,[],[f4663,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f4663,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f4661])).

fof(f4667,plain,
    ( spl4_158
    | ~ spl4_30
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f3832,f2922,f422,f3838])).

fof(f3838,plain,
    ( spl4_158
  <=> ! [X9] :
        ( ~ r2_hidden(X9,sK2)
        | r2_hidden(X9,k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f422,plain,
    ( spl4_30
  <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f2922,plain,
    ( spl4_122
  <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f3832,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl4_30
    | ~ spl4_122 ),
    inference(subsumption_resolution,[],[f3825,f397])).

fof(f397,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f205,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f58,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f59,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3825,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl4_30
    | ~ spl4_122 ),
    inference(resolution,[],[f2885,f2924])).

fof(f2924,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2885,plain,
    ( ! [X17,X18] :
        ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X17)
        | ~ r2_hidden(X18,sK2)
        | r2_hidden(X18,X17)
        | r2_hidden(X18,k1_tarski(sK0)) )
    | ~ spl4_30 ),
    inference(superposition,[],[f209,f424])).

fof(f424,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f422])).

fof(f209,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_tarski(k5_xboole_0(X11,X10),X12)
      | ~ r2_hidden(X9,X11)
      | r2_hidden(X9,X12)
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4664,plain,
    ( spl4_196
    | ~ spl4_30
    | ~ spl4_158 ),
    inference(avatar_split_clause,[],[f4659,f3838,f422,f4661])).

fof(f4659,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_30
    | ~ spl4_158 ),
    inference(duplicate_literal_removal,[],[f4652])).

fof(f4652,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_30
    | ~ spl4_158 ),
    inference(resolution,[],[f4650,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4650,plain,
    ( ! [X9] :
        ( r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),k1_tarski(sK0))
        | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X9) )
    | ~ spl4_30
    | ~ spl4_158 ),
    inference(subsumption_resolution,[],[f2879,f3839])).

fof(f3839,plain,
    ( ! [X9] :
        ( r2_hidden(X9,k1_tarski(sK0))
        | ~ r2_hidden(X9,sK2) )
    | ~ spl4_158 ),
    inference(avatar_component_clause,[],[f3838])).

fof(f2879,plain,
    ( ! [X9] :
        ( r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),k1_tarski(sK0))
        | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),sK2)
        | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X9) )
    | ~ spl4_30 ),
    inference(superposition,[],[f192,f424])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k5_xboole_0(X0,X1),X2),X1)
      | r2_hidden(sK3(k5_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3996,plain,
    ( spl4_163
    | ~ spl4_7
    | ~ spl4_141 ),
    inference(avatar_split_clause,[],[f3991,f3503,f127,f3993])).

fof(f3993,plain,
    ( spl4_163
  <=> sK2 = k5_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_163])])).

fof(f127,plain,
    ( spl4_7
  <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f3503,plain,
    ( spl4_141
  <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f3991,plain,
    ( sK2 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_141 ),
    inference(forward_demodulation,[],[f3960,f487])).

fof(f487,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f165,f184])).

fof(f184,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f183,f63])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f183,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f174,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f174,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f49,f46])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f165,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f47,f46])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3960,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2))
    | ~ spl4_7
    | ~ spl4_141 ),
    inference(superposition,[],[f2858,f3505])).

fof(f3505,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2))
    | ~ spl4_141 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f2858,plain,
    ( ! [X1] : k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X1) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),X1))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f2851,f184])).

fof(f2851,plain,
    ( ! [X1] : k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k5_xboole_0(k1_tarski(sK0),X1))
    | ~ spl4_7 ),
    inference(superposition,[],[f182,f129])).

fof(f129,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f182,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f47,f49])).

fof(f3911,plain,
    ( spl4_162
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f3887,f3495,f3908])).

fof(f3908,plain,
    ( spl4_162
  <=> k1_tarski(sK0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f3495,plain,
    ( spl4_140
  <=> k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f3887,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_140 ),
    inference(superposition,[],[f487,f3497])).

fof(f3497,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f3506,plain,
    ( spl4_141
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f3460,f127,f3503])).

fof(f3460,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f168,f2858])).

fof(f168,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f47,f46])).

fof(f3498,plain,
    ( spl4_140
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f3448,f127,f3495])).

fof(f3448,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(superposition,[],[f2858,f46])).

fof(f3350,plain,
    ( ~ spl4_134
    | ~ spl4_3
    | spl4_107 ),
    inference(avatar_split_clause,[],[f3349,f2659,f78,f3345])).

fof(f3345,plain,
    ( spl4_134
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f78,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2659,plain,
    ( spl4_107
  <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f3349,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_3
    | spl4_107 ),
    inference(forward_demodulation,[],[f2660,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f2660,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | spl4_107 ),
    inference(avatar_component_clause,[],[f2659])).

fof(f3272,plain,
    ( spl4_121
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f3268,f422,f2904])).

fof(f2904,plain,
    ( spl4_121
  <=> k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f3268,plain,
    ( k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_30 ),
    inference(superposition,[],[f487,f424])).

fof(f3231,plain,
    ( spl4_21
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f3224,f127,f306])).

fof(f306,plain,
    ( spl4_21
  <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f3224,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl4_7 ),
    inference(superposition,[],[f180,f129])).

fof(f180,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f49,f47])).

fof(f3228,plain,
    ( spl4_30
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f3227,f127,f422])).

fof(f3227,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f3220,f184])).

fof(f3220,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(superposition,[],[f49,f129])).

fof(f3213,plain,
    ( spl4_4
    | ~ spl4_128 ),
    inference(avatar_contradiction_clause,[],[f3208])).

fof(f3208,plain,
    ( $false
    | spl4_4
    | ~ spl4_128 ),
    inference(unit_resulting_resolution,[],[f84,f3042])).

fof(f3042,plain,
    ( ! [X3] : sK2 = k1_tarski(X3)
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f3041])).

fof(f3041,plain,
    ( spl4_128
  <=> ! [X3] : sK2 = k1_tarski(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f84,plain,
    ( sK2 != k1_tarski(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3110,plain,
    ( ~ spl4_118
    | ~ spl4_3
    | spl4_87 ),
    inference(avatar_split_clause,[],[f3109,f2078,f78,f2834])).

fof(f2834,plain,
    ( spl4_118
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f2078,plain,
    ( spl4_87
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f3109,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_3
    | spl4_87 ),
    inference(forward_demodulation,[],[f2079,f79])).

fof(f2079,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK2)
    | spl4_87 ),
    inference(avatar_component_clause,[],[f2078])).

fof(f3082,plain,
    ( ~ spl4_2
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f3080,f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_8
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f3080,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f3069,f48])).

fof(f3069,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f129,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3056,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3055,f2155,f78,f73])).

fof(f2155,plain,
    ( spl4_92
  <=> sK2 = k5_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f3055,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_92 ),
    inference(forward_demodulation,[],[f3054,f46])).

fof(f3054,plain,
    ( sK2 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_92 ),
    inference(forward_demodulation,[],[f2157,f79])).

fof(f2157,plain,
    ( sK2 = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f2155])).

fof(f3043,plain,
    ( spl4_128
    | spl4_2
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f3037,f2725,f73,f3041])).

fof(f2725,plain,
    ( spl4_112
  <=> k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f3037,plain,
    ( ! [X3] :
        ( k1_xboole_0 = sK2
        | sK2 = k1_tarski(X3) )
    | ~ spl4_112 ),
    inference(resolution,[],[f2985,f43])).

fof(f2985,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl4_112 ),
    inference(resolution,[],[f2970,f55])).

fof(f2970,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl4_112 ),
    inference(subsumption_resolution,[],[f2961,f397])).

fof(f2961,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl4_112 ),
    inference(duplicate_literal_removal,[],[f2940])).

fof(f2940,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl4_112 ),
    inference(superposition,[],[f60,f2727])).

fof(f2727,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f2725])).

fof(f2925,plain,
    ( spl4_122
    | ~ spl4_3
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f2920,f1366,f78,f2922])).

fof(f1366,plain,
    ( spl4_63
  <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f2920,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f1368,f79])).

fof(f1368,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1)
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f2862,plain,
    ( ~ spl4_3
    | spl4_93 ),
    inference(avatar_contradiction_clause,[],[f2861])).

fof(f2861,plain,
    ( $false
    | ~ spl4_3
    | spl4_93 ),
    inference(subsumption_resolution,[],[f2860,f46])).

fof(f2860,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | spl4_93 ),
    inference(forward_demodulation,[],[f2237,f79])).

fof(f2237,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | spl4_93 ),
    inference(avatar_component_clause,[],[f2236])).

fof(f2236,plain,
    ( spl4_93
  <=> sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f2844,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f2843,f88,f78,f127])).

fof(f88,plain,
    ( spl4_5
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2843,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f90,f79])).

fof(f90,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f2839,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f2838,f78,f69,f132])).

fof(f69,plain,
    ( spl4_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2838,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f71,f79])).

fof(f71,plain,
    ( sK1 != k1_tarski(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f2792,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k1_tarski(sK0))
    | k1_xboole_0 != sK1
    | k3_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0)))
    | k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2769,plain,
    ( sK1 != k5_xboole_0(sK1,sK2)
    | k5_xboole_0(sK2,sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k5_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK1,sK2) != k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2728,plain,
    ( spl4_112
    | ~ spl4_49
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f2702,f2654,f710,f2725])).

fof(f710,plain,
    ( spl4_49
  <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f2654,plain,
    ( spl4_106
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f2702,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_49
    | ~ spl4_106 ),
    inference(backward_demodulation,[],[f712,f2656])).

fof(f2656,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f2654])).

fof(f712,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f710])).

fof(f2657,plain,
    ( spl4_106
    | ~ spl4_13
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f2625,f1960,f188,f2654])).

fof(f188,plain,
    ( spl4_13
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1960,plain,
    ( spl4_78
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f2625,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_13
    | ~ spl4_78 ),
    inference(backward_demodulation,[],[f190,f1962])).

fof(f1962,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f1960])).

fof(f190,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f2317,plain,
    ( spl4_78
    | ~ spl4_1
    | ~ spl4_36
    | spl4_77 ),
    inference(avatar_split_clause,[],[f2316,f1956,f562,f69,f1960])).

fof(f562,plain,
    ( spl4_36
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1956,plain,
    ( spl4_77
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f2316,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl4_1
    | ~ spl4_36
    | spl4_77 ),
    inference(subsumption_resolution,[],[f2288,f1957])).

fof(f1957,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl4_77 ),
    inference(avatar_component_clause,[],[f1956])).

fof(f2288,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_36 ),
    inference(superposition,[],[f564,f476])).

fof(f476,plain,
    ( ! [X3] :
        ( sK1 = k4_xboole_0(sK1,X3)
        | k1_xboole_0 = k4_xboole_0(sK1,X3) )
    | ~ spl4_1 ),
    inference(resolution,[],[f432,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f432,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | k1_xboole_0 = X1
        | sK1 = X1 )
    | ~ spl4_1 ),
    inference(superposition,[],[f43,f70])).

fof(f70,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f564,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f562])).

fof(f2202,plain,
    ( spl4_33
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f2196,f188,f506])).

fof(f506,plain,
    ( spl4_33
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f2196,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl4_13 ),
    inference(superposition,[],[f487,f190])).

fof(f2199,plain,
    ( spl4_36
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f2198,f188,f562])).

fof(f2198,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f2178,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2178,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl4_13 ),
    inference(superposition,[],[f168,f190])).

fof(f2161,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | sK2 != k5_xboole_0(sK1,k1_xboole_0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2158,plain,
    ( spl4_92
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f2124,f2078,f2155])).

fof(f2124,plain,
    ( sK2 = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_87 ),
    inference(superposition,[],[f487,f2080])).

fof(f2080,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f2078])).

fof(f2086,plain,
    ( spl4_88
    | spl4_87
    | ~ spl4_1
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f2073,f1980,f69,f2078,f2083])).

fof(f2083,plain,
    ( spl4_88
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1980,plain,
    ( spl4_80
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f2073,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_80 ),
    inference(resolution,[],[f2055,f432])).

fof(f2055,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK1,sK2),X0)
    | ~ spl4_80 ),
    inference(resolution,[],[f2040,f55])).

fof(f2040,plain,
    ( ! [X3] : ~ r2_hidden(X3,k5_xboole_0(sK1,sK2))
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f2023,f397])).

fof(f2023,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k5_xboole_0(sK1,sK2)) )
    | ~ spl4_80 ),
    inference(duplicate_literal_removal,[],[f2002])).

fof(f2002,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k5_xboole_0(sK1,sK2)) )
    | ~ spl4_80 ),
    inference(superposition,[],[f60,f1982])).

fof(f1982,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1980])).

fof(f1983,plain,
    ( spl4_80
    | ~ spl4_36
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f1969,f1956,f562,f1980])).

fof(f1969,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl4_36
    | ~ spl4_77 ),
    inference(backward_demodulation,[],[f564,f1958])).

fof(f1958,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f1956])).

fof(f1780,plain,
    ( spl4_52
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f1771,f710,f768])).

fof(f768,plain,
    ( spl4_52
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1771,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_49 ),
    inference(superposition,[],[f487,f712])).

fof(f1744,plain,
    ( spl4_45
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f1730,f241,f678])).

fof(f678,plain,
    ( spl4_45
  <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f241,plain,
    ( spl4_14
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1730,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1729,f62])).

fof(f1729,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1707,f47])).

fof(f1707,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_14 ),
    inference(superposition,[],[f168,f243])).

fof(f243,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1738,plain,
    ( spl4_70
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f1725,f241,f1735])).

fof(f1735,plain,
    ( spl4_70
  <=> k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1725,plain,
    ( k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl4_14 ),
    inference(superposition,[],[f487,f243])).

fof(f1733,plain,
    ( spl4_49
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f1695,f241,f710])).

fof(f1695,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl4_14 ),
    inference(superposition,[],[f168,f243])).

fof(f1369,plain,
    ( spl4_63
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f1358,f1200,f1366])).

fof(f1200,plain,
    ( spl4_59
  <=> k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f1358,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1)
    | ~ spl4_59 ),
    inference(superposition,[],[f57,f1202])).

fof(f1202,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1268,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f643,f158,f241])).

fof(f158,plain,
    ( spl4_12
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f643,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl4_12 ),
    inference(superposition,[],[f180,f160])).

fof(f160,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1204,plain,
    ( spl4_59
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1183,f606,f1200])).

fof(f606,plain,
    ( spl4_41
  <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1183,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl4_41 ),
    inference(superposition,[],[f62,f608])).

fof(f608,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f606])).

fof(f631,plain,
    ( spl4_42
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f617,f506,f627])).

fof(f627,plain,
    ( spl4_42
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f617,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl4_33 ),
    inference(superposition,[],[f47,f508])).

fof(f508,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f506])).

fof(f439,plain,
    ( spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f437,f158,f188])).

fof(f437,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f49,f160])).

fof(f161,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f156,f88,f69,f158])).

fof(f156,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f90,f70])).

fof(f145,plain,
    ( ~ spl4_9
    | ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f137,f82,f69,f142])).

fof(f142,plain,
    ( spl4_9
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f137,plain,
    ( sK1 != sK2
    | ~ spl4_1
    | spl4_4 ),
    inference(backward_demodulation,[],[f84,f70])).

fof(f136,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f118,f95,f78,f69])).

fof(f95,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f43,f97])).

fof(f97,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f98,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f92,f88,f95])).

fof(f92,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f51,f90])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f91,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f86,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f40,f82,f69])).

fof(f40,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f41,f82,f78])).

fof(f41,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f73,f69])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

% (411)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (32689)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.48  % (32696)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (32706)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.49  % (32714)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.49  % (32698)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.49  % (32694)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (32699)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (32695)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (32690)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (32698)Refutation not found, incomplete strategy% (32698)------------------------------
% 0.20/0.50  % (32698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32688)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (32698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32698)Memory used [KB]: 10618
% 0.20/0.50  % (32698)Time elapsed: 0.064 s
% 0.20/0.50  % (32698)------------------------------
% 0.20/0.50  % (32698)------------------------------
% 0.20/0.50  % (32697)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (32701)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (32690)Refutation not found, incomplete strategy% (32690)------------------------------
% 0.20/0.50  % (32690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (32690)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32690)Memory used [KB]: 10746
% 0.20/0.50  % (32690)Time elapsed: 0.079 s
% 0.20/0.50  % (32690)------------------------------
% 0.20/0.50  % (32690)------------------------------
% 0.20/0.50  % (32707)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (32710)Refutation not found, incomplete strategy% (32710)------------------------------
% 0.20/0.50  % (32710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32710)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32710)Memory used [KB]: 10746
% 0.20/0.50  % (32710)Time elapsed: 0.109 s
% 0.20/0.50  % (32710)------------------------------
% 0.20/0.50  % (32710)------------------------------
% 0.20/0.51  % (32715)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (32699)Refutation not found, incomplete strategy% (32699)------------------------------
% 0.20/0.51  % (32699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32699)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32699)Memory used [KB]: 10618
% 0.20/0.51  % (32699)Time elapsed: 0.108 s
% 0.20/0.51  % (32699)------------------------------
% 0.20/0.51  % (32699)------------------------------
% 0.20/0.51  % (32716)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (32717)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (32712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (32692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (32691)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (32709)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (32693)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (32703)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (32705)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (32708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (32703)Refutation not found, incomplete strategy% (32703)------------------------------
% 0.20/0.52  % (32703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32703)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32703)Memory used [KB]: 6140
% 0.20/0.52  % (32703)Time elapsed: 0.004 s
% 0.20/0.52  % (32703)------------------------------
% 0.20/0.52  % (32703)------------------------------
% 0.20/0.52  % (32713)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (32711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (32700)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (32704)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (32709)Refutation not found, incomplete strategy% (32709)------------------------------
% 0.20/0.53  % (32709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32709)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32709)Memory used [KB]: 1791
% 0.20/0.53  % (32709)Time elapsed: 0.135 s
% 0.20/0.53  % (32709)------------------------------
% 0.20/0.53  % (32709)------------------------------
% 0.20/0.53  % (32702)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.86/0.61  % (32730)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.86/0.62  % (32732)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.05/0.65  % (32735)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.05/0.65  % (32733)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.05/0.67  % (32748)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.05/0.67  % (32742)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.33/0.82  % (32693)Time limit reached!
% 3.33/0.82  % (32693)------------------------------
% 3.33/0.82  % (32693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.82  % (32693)Termination reason: Time limit
% 3.33/0.82  
% 3.33/0.82  % (32693)Memory used [KB]: 10618
% 3.33/0.82  % (32693)Time elapsed: 0.420 s
% 3.33/0.82  % (32693)------------------------------
% 3.33/0.82  % (32693)------------------------------
% 3.95/0.90  % (32689)Time limit reached!
% 3.95/0.90  % (32689)------------------------------
% 3.95/0.90  % (32689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.90  % (32688)Time limit reached!
% 4.16/0.90  % (32688)------------------------------
% 4.16/0.90  % (32688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (32688)Termination reason: Time limit
% 4.16/0.91  % (32688)Termination phase: Saturation
% 4.16/0.91  
% 4.16/0.91  % (32688)Memory used [KB]: 2430
% 4.16/0.91  % (32688)Time elapsed: 0.500 s
% 4.16/0.91  % (32688)------------------------------
% 4.16/0.91  % (32688)------------------------------
% 4.16/0.91  % (32700)Time limit reached!
% 4.16/0.91  % (32700)------------------------------
% 4.16/0.91  % (32700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (32700)Termination reason: Time limit
% 4.16/0.91  
% 4.16/0.91  % (32700)Memory used [KB]: 11257
% 4.16/0.91  % (32700)Time elapsed: 0.517 s
% 4.16/0.91  % (32700)------------------------------
% 4.16/0.91  % (32700)------------------------------
% 4.16/0.91  % (32689)Termination reason: Time limit
% 4.16/0.91  % (32689)Termination phase: Saturation
% 4.16/0.91  
% 4.16/0.91  % (32689)Memory used [KB]: 9083
% 4.16/0.91  % (32689)Time elapsed: 0.500 s
% 4.16/0.91  % (32689)------------------------------
% 4.16/0.91  % (32689)------------------------------
% 4.40/0.93  % (32705)Time limit reached!
% 4.40/0.93  % (32705)------------------------------
% 4.40/0.93  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.93  % (32705)Termination reason: Time limit
% 4.40/0.93  % (32705)Termination phase: Saturation
% 4.40/0.93  
% 4.40/0.93  % (32705)Memory used [KB]: 17654
% 4.40/0.93  % (32705)Time elapsed: 0.500 s
% 4.40/0.93  % (32705)------------------------------
% 4.40/0.93  % (32705)------------------------------
% 4.40/0.95  % (32735)Time limit reached!
% 4.40/0.95  % (32735)------------------------------
% 4.40/0.95  % (32735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.95  % (32733)Refutation found. Thanks to Tanya!
% 4.40/0.95  % SZS status Theorem for theBenchmark
% 4.40/0.96  % SZS output start Proof for theBenchmark
% 4.40/0.96  % (32735)Termination reason: Time limit
% 4.40/0.96  
% 4.40/0.96  % (32735)Memory used [KB]: 8571
% 4.40/0.96  % (32735)Time elapsed: 0.424 s
% 4.40/0.96  % (32735)------------------------------
% 4.40/0.96  % (32735)------------------------------
% 4.40/0.96  fof(f4689,plain,(
% 4.40/0.96    $false),
% 4.40/0.96    inference(avatar_sat_refutation,[],[f76,f85,f86,f91,f98,f136,f145,f161,f439,f631,f1204,f1268,f1369,f1733,f1738,f1744,f1780,f1983,f2086,f2158,f2161,f2199,f2202,f2317,f2657,f2728,f2769,f2792,f2839,f2844,f2862,f2925,f3043,f3056,f3082,f3110,f3213,f3228,f3231,f3272,f3350,f3498,f3506,f3911,f3996,f4664,f4667,f4676,f4679,f4683,f4688])).
% 4.40/0.96  fof(f4688,plain,(
% 4.40/0.96    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2) | k1_xboole_0 != sK1 | sK2 != k5_xboole_0(sK2,k1_xboole_0) | k1_tarski(sK0) != k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) | sK2 = k1_tarski(sK0)),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f4683,plain,(
% 4.40/0.96    sK2 != k5_xboole_0(sK2,k1_xboole_0) | k1_xboole_0 != sK1 | k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f4679,plain,(
% 4.40/0.96    k1_tarski(sK0) != k3_xboole_0(k1_xboole_0,sK2) | sK2 != k5_xboole_0(sK2,k1_xboole_0) | k1_tarski(sK0) != k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0)) | k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2)) | sK1 != k5_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 != sK1 | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f4676,plain,(
% 4.40/0.96    spl4_197 | spl4_81 | ~spl4_196),
% 4.40/0.96    inference(avatar_split_clause,[],[f4671,f4661,f1985,f4673])).
% 4.40/0.96  fof(f4673,plain,(
% 4.40/0.96    spl4_197 <=> k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).
% 4.40/0.96  fof(f1985,plain,(
% 4.40/0.96    spl4_81 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 4.40/0.96  fof(f4661,plain,(
% 4.40/0.96    spl4_196 <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).
% 4.40/0.96  fof(f4671,plain,(
% 4.40/0.96    k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2) | (spl4_81 | ~spl4_196)),
% 4.40/0.96    inference(subsumption_resolution,[],[f4668,f1987])).
% 4.40/0.96  fof(f1987,plain,(
% 4.40/0.96    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2) | spl4_81),
% 4.40/0.96    inference(avatar_component_clause,[],[f1985])).
% 4.40/0.96  fof(f4668,plain,(
% 4.40/0.96    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,sK2) | ~spl4_196),
% 4.40/0.96    inference(resolution,[],[f4663,f43])).
% 4.40/0.96  fof(f43,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.40/0.96    inference(cnf_transformation,[],[f33])).
% 4.40/0.96  fof(f33,plain,(
% 4.40/0.96    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.40/0.96    inference(flattening,[],[f32])).
% 4.40/0.96  fof(f32,plain,(
% 4.40/0.96    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.40/0.96    inference(nnf_transformation,[],[f19])).
% 4.40/0.96  fof(f19,axiom,(
% 4.40/0.96    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 4.40/0.96  fof(f4663,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | ~spl4_196),
% 4.40/0.96    inference(avatar_component_clause,[],[f4661])).
% 4.40/0.96  fof(f4667,plain,(
% 4.40/0.96    spl4_158 | ~spl4_30 | ~spl4_122),
% 4.40/0.96    inference(avatar_split_clause,[],[f3832,f2922,f422,f3838])).
% 4.40/0.96  fof(f3838,plain,(
% 4.40/0.96    spl4_158 <=> ! [X9] : (~r2_hidden(X9,sK2) | r2_hidden(X9,k1_tarski(sK0)))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).
% 4.40/0.96  fof(f422,plain,(
% 4.40/0.96    spl4_30 <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 4.40/0.96  fof(f2922,plain,(
% 4.40/0.96    spl4_122 <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).
% 4.40/0.96  fof(f3832,plain,(
% 4.40/0.96    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k1_tarski(sK0))) ) | (~spl4_30 | ~spl4_122)),
% 4.40/0.96    inference(subsumption_resolution,[],[f3825,f397])).
% 4.40/0.96  fof(f397,plain,(
% 4.40/0.96    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 4.40/0.96    inference(subsumption_resolution,[],[f205,f197])).
% 4.40/0.96  fof(f197,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 4.40/0.96    inference(duplicate_literal_removal,[],[f193])).
% 4.40/0.96  fof(f193,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | r2_hidden(X1,X0)) )),
% 4.40/0.96    inference(superposition,[],[f58,f46])).
% 4.40/0.96  fof(f46,plain,(
% 4.40/0.96    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 4.40/0.96    inference(cnf_transformation,[],[f10])).
% 4.40/0.96  fof(f10,axiom,(
% 4.40/0.96    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.40/0.96  fof(f58,plain,(
% 4.40/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f38])).
% 4.40/0.96  fof(f38,plain,(
% 4.40/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.40/0.96    inference(nnf_transformation,[],[f29])).
% 4.40/0.96  fof(f29,plain,(
% 4.40/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.40/0.96    inference(ennf_transformation,[],[f4])).
% 4.40/0.96  fof(f4,axiom,(
% 4.40/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.40/0.96  fof(f205,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 4.40/0.96    inference(duplicate_literal_removal,[],[f201])).
% 4.40/0.96  fof(f201,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 4.40/0.96    inference(superposition,[],[f59,f46])).
% 4.40/0.96  fof(f59,plain,(
% 4.40/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f38])).
% 4.40/0.96  fof(f3825,plain,(
% 4.40/0.96    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k1_tarski(sK0))) ) | (~spl4_30 | ~spl4_122)),
% 4.40/0.96    inference(resolution,[],[f2885,f2924])).
% 4.40/0.96  fof(f2924,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | ~spl4_122),
% 4.40/0.96    inference(avatar_component_clause,[],[f2922])).
% 4.40/0.96  fof(f2885,plain,(
% 4.40/0.96    ( ! [X17,X18] : (~r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X17) | ~r2_hidden(X18,sK2) | r2_hidden(X18,X17) | r2_hidden(X18,k1_tarski(sK0))) ) | ~spl4_30),
% 4.40/0.96    inference(superposition,[],[f209,f424])).
% 4.40/0.96  fof(f424,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0)) | ~spl4_30),
% 4.40/0.96    inference(avatar_component_clause,[],[f422])).
% 4.40/0.96  fof(f209,plain,(
% 4.40/0.96    ( ! [X12,X10,X11,X9] : (~r1_tarski(k5_xboole_0(X11,X10),X12) | ~r2_hidden(X9,X11) | r2_hidden(X9,X12) | r2_hidden(X9,X10)) )),
% 4.40/0.96    inference(resolution,[],[f60,f54])).
% 4.40/0.96  fof(f54,plain,(
% 4.40/0.96    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f37])).
% 4.40/0.96  fof(f37,plain,(
% 4.40/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.40/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 4.40/0.96  fof(f36,plain,(
% 4.40/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 4.40/0.96    introduced(choice_axiom,[])).
% 4.40/0.96  fof(f35,plain,(
% 4.40/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.40/0.96    inference(rectify,[],[f34])).
% 4.40/0.96  fof(f34,plain,(
% 4.40/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.40/0.96    inference(nnf_transformation,[],[f28])).
% 4.40/0.96  fof(f28,plain,(
% 4.40/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.40/0.96    inference(ennf_transformation,[],[f1])).
% 4.40/0.96  fof(f1,axiom,(
% 4.40/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 4.40/0.96  fof(f60,plain,(
% 4.40/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f38])).
% 4.40/0.96  fof(f4664,plain,(
% 4.40/0.96    spl4_196 | ~spl4_30 | ~spl4_158),
% 4.40/0.96    inference(avatar_split_clause,[],[f4659,f3838,f422,f4661])).
% 4.40/0.96  fof(f4659,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | (~spl4_30 | ~spl4_158)),
% 4.40/0.96    inference(duplicate_literal_removal,[],[f4652])).
% 4.40/0.96  fof(f4652,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | (~spl4_30 | ~spl4_158)),
% 4.40/0.96    inference(resolution,[],[f4650,f56])).
% 4.40/0.96  fof(f56,plain,(
% 4.40/0.96    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f37])).
% 4.40/0.96  fof(f4650,plain,(
% 4.40/0.96    ( ! [X9] : (r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),k1_tarski(sK0)) | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X9)) ) | (~spl4_30 | ~spl4_158)),
% 4.40/0.96    inference(subsumption_resolution,[],[f2879,f3839])).
% 4.40/0.96  fof(f3839,plain,(
% 4.40/0.96    ( ! [X9] : (r2_hidden(X9,k1_tarski(sK0)) | ~r2_hidden(X9,sK2)) ) | ~spl4_158),
% 4.40/0.96    inference(avatar_component_clause,[],[f3838])).
% 4.40/0.96  fof(f2879,plain,(
% 4.40/0.96    ( ! [X9] : (r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),k1_tarski(sK0)) | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,sK2),X9),sK2) | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),X9)) ) | ~spl4_30),
% 4.40/0.96    inference(superposition,[],[f192,f424])).
% 4.40/0.96  fof(f192,plain,(
% 4.40/0.96    ( ! [X2,X0,X1] : (r2_hidden(sK3(k5_xboole_0(X0,X1),X2),X1) | r2_hidden(sK3(k5_xboole_0(X0,X1),X2),X0) | r1_tarski(k5_xboole_0(X0,X1),X2)) )),
% 4.40/0.96    inference(resolution,[],[f58,f55])).
% 4.40/0.96  fof(f55,plain,(
% 4.40/0.96    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f37])).
% 4.40/0.96  fof(f3996,plain,(
% 4.40/0.96    spl4_163 | ~spl4_7 | ~spl4_141),
% 4.40/0.96    inference(avatar_split_clause,[],[f3991,f3503,f127,f3993])).
% 4.40/0.96  fof(f3993,plain,(
% 4.40/0.96    spl4_163 <=> sK2 = k5_xboole_0(sK2,k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_163])])).
% 4.40/0.96  fof(f127,plain,(
% 4.40/0.96    spl4_7 <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 4.40/0.96  fof(f3503,plain,(
% 4.40/0.96    spl4_141 <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 4.40/0.96  fof(f3991,plain,(
% 4.40/0.96    sK2 = k5_xboole_0(sK2,k1_xboole_0) | (~spl4_7 | ~spl4_141)),
% 4.40/0.96    inference(forward_demodulation,[],[f3960,f487])).
% 4.40/0.96  fof(f487,plain,(
% 4.40/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.40/0.96    inference(forward_demodulation,[],[f165,f184])).
% 4.40/0.96  fof(f184,plain,(
% 4.40/0.96    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.40/0.96    inference(forward_demodulation,[],[f183,f63])).
% 4.40/0.96  fof(f63,plain,(
% 4.40/0.96    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.40/0.96    inference(cnf_transformation,[],[f24])).
% 4.40/0.96  fof(f24,plain,(
% 4.40/0.96    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.40/0.96    inference(rectify,[],[f3])).
% 4.40/0.96  fof(f3,axiom,(
% 4.40/0.96    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.40/0.96  fof(f183,plain,(
% 4.40/0.96    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.40/0.96    inference(forward_demodulation,[],[f174,f48])).
% 4.40/0.96  fof(f48,plain,(
% 4.40/0.96    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.40/0.96    inference(cnf_transformation,[],[f23])).
% 4.40/0.96  fof(f23,plain,(
% 4.40/0.96    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.40/0.96    inference(rectify,[],[f2])).
% 4.40/0.96  fof(f2,axiom,(
% 4.40/0.96    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.40/0.96  fof(f174,plain,(
% 4.40/0.96    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 4.40/0.96    inference(superposition,[],[f49,f46])).
% 4.40/0.96  fof(f49,plain,(
% 4.40/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.40/0.96    inference(cnf_transformation,[],[f11])).
% 4.40/0.96  fof(f11,axiom,(
% 4.40/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.40/0.96  fof(f165,plain,(
% 4.40/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 4.40/0.96    inference(superposition,[],[f47,f46])).
% 4.40/0.96  fof(f47,plain,(
% 4.40/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.40/0.96    inference(cnf_transformation,[],[f9])).
% 4.40/0.96  fof(f9,axiom,(
% 4.40/0.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.40/0.96  fof(f3960,plain,(
% 4.40/0.96    k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2)) | (~spl4_7 | ~spl4_141)),
% 4.40/0.96    inference(superposition,[],[f2858,f3505])).
% 4.40/0.96  fof(f3505,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2)) | ~spl4_141),
% 4.40/0.96    inference(avatar_component_clause,[],[f3503])).
% 4.40/0.96  fof(f2858,plain,(
% 4.40/0.96    ( ! [X1] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X1) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),X1))) ) | ~spl4_7),
% 4.40/0.96    inference(forward_demodulation,[],[f2851,f184])).
% 4.40/0.96  fof(f2851,plain,(
% 4.40/0.96    ( ! [X1] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k5_xboole_0(k1_tarski(sK0),X1))) ) | ~spl4_7),
% 4.40/0.96    inference(superposition,[],[f182,f129])).
% 4.40/0.96  fof(f129,plain,(
% 4.40/0.96    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | ~spl4_7),
% 4.40/0.96    inference(avatar_component_clause,[],[f127])).
% 4.40/0.96  fof(f182,plain,(
% 4.40/0.96    ( ! [X4,X2,X3] : (k5_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 4.40/0.96    inference(superposition,[],[f47,f49])).
% 4.40/0.96  fof(f3911,plain,(
% 4.40/0.96    spl4_162 | ~spl4_140),
% 4.40/0.96    inference(avatar_split_clause,[],[f3887,f3495,f3908])).
% 4.40/0.96  fof(f3908,plain,(
% 4.40/0.96    spl4_162 <=> k1_tarski(sK0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).
% 4.40/0.96  fof(f3495,plain,(
% 4.40/0.96    spl4_140 <=> k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).
% 4.40/0.96  fof(f3887,plain,(
% 4.40/0.96    k1_tarski(sK0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k5_xboole_0(sK2,k1_xboole_0)) | ~spl4_140),
% 4.40/0.96    inference(superposition,[],[f487,f3497])).
% 4.40/0.96  fof(f3497,plain,(
% 4.40/0.96    k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | ~spl4_140),
% 4.40/0.96    inference(avatar_component_clause,[],[f3495])).
% 4.40/0.96  fof(f3506,plain,(
% 4.40/0.96    spl4_141 | ~spl4_7),
% 4.40/0.96    inference(avatar_split_clause,[],[f3460,f127,f3503])).
% 4.40/0.96  fof(f3460,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2)) | ~spl4_7),
% 4.40/0.96    inference(superposition,[],[f168,f2858])).
% 4.40/0.96  fof(f168,plain,(
% 4.40/0.96    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 4.40/0.96    inference(superposition,[],[f47,f46])).
% 4.40/0.96  fof(f3498,plain,(
% 4.40/0.96    spl4_140 | ~spl4_7),
% 4.40/0.96    inference(avatar_split_clause,[],[f3448,f127,f3495])).
% 4.40/0.96  fof(f3448,plain,(
% 4.40/0.96    k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | ~spl4_7),
% 4.40/0.96    inference(superposition,[],[f2858,f46])).
% 4.40/0.96  fof(f3350,plain,(
% 4.40/0.96    ~spl4_134 | ~spl4_3 | spl4_107),
% 4.40/0.96    inference(avatar_split_clause,[],[f3349,f2659,f78,f3345])).
% 4.40/0.96  fof(f3345,plain,(
% 4.40/0.96    spl4_134 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 4.40/0.96  fof(f78,plain,(
% 4.40/0.96    spl4_3 <=> k1_xboole_0 = sK1),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.40/0.96  fof(f2659,plain,(
% 4.40/0.96    spl4_107 <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 4.40/0.96  fof(f3349,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) | (~spl4_3 | spl4_107)),
% 4.40/0.96    inference(forward_demodulation,[],[f2660,f79])).
% 4.40/0.96  fof(f79,plain,(
% 4.40/0.96    k1_xboole_0 = sK1 | ~spl4_3),
% 4.40/0.96    inference(avatar_component_clause,[],[f78])).
% 4.40/0.96  fof(f2660,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | spl4_107),
% 4.40/0.96    inference(avatar_component_clause,[],[f2659])).
% 4.40/0.96  fof(f3272,plain,(
% 4.40/0.96    spl4_121 | ~spl4_30),
% 4.40/0.96    inference(avatar_split_clause,[],[f3268,f422,f2904])).
% 4.40/0.96  fof(f2904,plain,(
% 4.40/0.96    spl4_121 <=> k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 4.40/0.96  fof(f3268,plain,(
% 4.40/0.96    k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) | ~spl4_30),
% 4.40/0.96    inference(superposition,[],[f487,f424])).
% 4.40/0.96  fof(f3231,plain,(
% 4.40/0.96    spl4_21 | ~spl4_7),
% 4.40/0.96    inference(avatar_split_clause,[],[f3224,f127,f306])).
% 4.40/0.96  fof(f306,plain,(
% 4.40/0.96    spl4_21 <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0)))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 4.40/0.96  fof(f3224,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0))) | ~spl4_7),
% 4.40/0.96    inference(superposition,[],[f180,f129])).
% 4.40/0.96  fof(f180,plain,(
% 4.40/0.96    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 4.40/0.96    inference(superposition,[],[f49,f47])).
% 4.40/0.96  fof(f3228,plain,(
% 4.40/0.96    spl4_30 | ~spl4_7),
% 4.40/0.96    inference(avatar_split_clause,[],[f3227,f127,f422])).
% 4.40/0.96  fof(f3227,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k1_tarski(sK0)) | ~spl4_7),
% 4.40/0.96    inference(forward_demodulation,[],[f3220,f184])).
% 4.40/0.96  fof(f3220,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) | ~spl4_7),
% 4.40/0.96    inference(superposition,[],[f49,f129])).
% 4.40/0.96  fof(f3213,plain,(
% 4.40/0.96    spl4_4 | ~spl4_128),
% 4.40/0.96    inference(avatar_contradiction_clause,[],[f3208])).
% 4.40/0.96  fof(f3208,plain,(
% 4.40/0.96    $false | (spl4_4 | ~spl4_128)),
% 4.40/0.96    inference(unit_resulting_resolution,[],[f84,f3042])).
% 4.40/0.96  fof(f3042,plain,(
% 4.40/0.96    ( ! [X3] : (sK2 = k1_tarski(X3)) ) | ~spl4_128),
% 4.40/0.96    inference(avatar_component_clause,[],[f3041])).
% 4.40/0.96  fof(f3041,plain,(
% 4.40/0.96    spl4_128 <=> ! [X3] : sK2 = k1_tarski(X3)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).
% 4.40/0.96  fof(f84,plain,(
% 4.40/0.96    sK2 != k1_tarski(sK0) | spl4_4),
% 4.40/0.96    inference(avatar_component_clause,[],[f82])).
% 4.40/0.96  fof(f82,plain,(
% 4.40/0.96    spl4_4 <=> sK2 = k1_tarski(sK0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 4.40/0.96  fof(f3110,plain,(
% 4.40/0.96    ~spl4_118 | ~spl4_3 | spl4_87),
% 4.40/0.96    inference(avatar_split_clause,[],[f3109,f2078,f78,f2834])).
% 4.40/0.96  fof(f2834,plain,(
% 4.40/0.96    spl4_118 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 4.40/0.96  fof(f2078,plain,(
% 4.40/0.96    spl4_87 <=> k1_xboole_0 = k5_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 4.40/0.96  fof(f3109,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(k1_xboole_0,sK2) | (~spl4_3 | spl4_87)),
% 4.40/0.96    inference(forward_demodulation,[],[f2079,f79])).
% 4.40/0.96  fof(f2079,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(sK1,sK2) | spl4_87),
% 4.40/0.96    inference(avatar_component_clause,[],[f2078])).
% 4.40/0.96  fof(f3082,plain,(
% 4.40/0.96    ~spl4_2 | ~spl4_7 | spl4_8),
% 4.40/0.96    inference(avatar_contradiction_clause,[],[f3081])).
% 4.40/0.96  fof(f3081,plain,(
% 4.40/0.96    $false | (~spl4_2 | ~spl4_7 | spl4_8)),
% 4.40/0.96    inference(subsumption_resolution,[],[f3080,f134])).
% 4.40/0.96  fof(f134,plain,(
% 4.40/0.96    k1_xboole_0 != k1_tarski(sK0) | spl4_8),
% 4.40/0.96    inference(avatar_component_clause,[],[f132])).
% 4.40/0.96  fof(f132,plain,(
% 4.40/0.96    spl4_8 <=> k1_xboole_0 = k1_tarski(sK0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 4.40/0.96  fof(f3080,plain,(
% 4.40/0.96    k1_xboole_0 = k1_tarski(sK0) | (~spl4_2 | ~spl4_7)),
% 4.40/0.96    inference(forward_demodulation,[],[f3069,f48])).
% 4.40/0.96  fof(f3069,plain,(
% 4.40/0.96    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_2 | ~spl4_7)),
% 4.40/0.96    inference(backward_demodulation,[],[f129,f74])).
% 4.40/0.96  fof(f74,plain,(
% 4.40/0.96    k1_xboole_0 = sK2 | ~spl4_2),
% 4.40/0.96    inference(avatar_component_clause,[],[f73])).
% 4.40/0.96  fof(f73,plain,(
% 4.40/0.96    spl4_2 <=> k1_xboole_0 = sK2),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.40/0.96  fof(f3056,plain,(
% 4.40/0.96    spl4_2 | ~spl4_3 | ~spl4_92),
% 4.40/0.96    inference(avatar_split_clause,[],[f3055,f2155,f78,f73])).
% 4.40/0.96  fof(f2155,plain,(
% 4.40/0.96    spl4_92 <=> sK2 = k5_xboole_0(sK1,k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 4.40/0.96  fof(f3055,plain,(
% 4.40/0.96    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_92)),
% 4.40/0.96    inference(forward_demodulation,[],[f3054,f46])).
% 4.40/0.96  fof(f3054,plain,(
% 4.40/0.96    sK2 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_92)),
% 4.40/0.96    inference(forward_demodulation,[],[f2157,f79])).
% 4.40/0.96  fof(f2157,plain,(
% 4.40/0.96    sK2 = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_92),
% 4.40/0.96    inference(avatar_component_clause,[],[f2155])).
% 4.40/0.96  fof(f3043,plain,(
% 4.40/0.96    spl4_128 | spl4_2 | ~spl4_112),
% 4.40/0.96    inference(avatar_split_clause,[],[f3037,f2725,f73,f3041])).
% 4.40/0.96  fof(f2725,plain,(
% 4.40/0.96    spl4_112 <=> k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 4.40/0.96  fof(f3037,plain,(
% 4.40/0.96    ( ! [X3] : (k1_xboole_0 = sK2 | sK2 = k1_tarski(X3)) ) | ~spl4_112),
% 4.40/0.96    inference(resolution,[],[f2985,f43])).
% 4.40/0.96  fof(f2985,plain,(
% 4.40/0.96    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl4_112),
% 4.40/0.96    inference(resolution,[],[f2970,f55])).
% 4.40/0.96  fof(f2970,plain,(
% 4.40/0.96    ( ! [X3] : (~r2_hidden(X3,sK2)) ) | ~spl4_112),
% 4.40/0.96    inference(subsumption_resolution,[],[f2961,f397])).
% 4.40/0.96  fof(f2961,plain,(
% 4.40/0.96    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK2)) ) | ~spl4_112),
% 4.40/0.96    inference(duplicate_literal_removal,[],[f2940])).
% 4.40/0.96  fof(f2940,plain,(
% 4.40/0.96    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK2)) ) | ~spl4_112),
% 4.40/0.96    inference(superposition,[],[f60,f2727])).
% 4.40/0.96  fof(f2727,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | ~spl4_112),
% 4.40/0.96    inference(avatar_component_clause,[],[f2725])).
% 4.40/0.96  fof(f2925,plain,(
% 4.40/0.96    spl4_122 | ~spl4_3 | ~spl4_63),
% 4.40/0.96    inference(avatar_split_clause,[],[f2920,f1366,f78,f2922])).
% 4.40/0.96  fof(f1366,plain,(
% 4.40/0.96    spl4_63 <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 4.40/0.96  fof(f2920,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | (~spl4_3 | ~spl4_63)),
% 4.40/0.96    inference(forward_demodulation,[],[f1368,f79])).
% 4.40/0.96  fof(f1368,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1) | ~spl4_63),
% 4.40/0.96    inference(avatar_component_clause,[],[f1366])).
% 4.40/0.96  fof(f2862,plain,(
% 4.40/0.96    ~spl4_3 | spl4_93),
% 4.40/0.96    inference(avatar_contradiction_clause,[],[f2861])).
% 4.40/0.96  fof(f2861,plain,(
% 4.40/0.96    $false | (~spl4_3 | spl4_93)),
% 4.40/0.96    inference(subsumption_resolution,[],[f2860,f46])).
% 4.40/0.96  fof(f2860,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_3 | spl4_93)),
% 4.40/0.96    inference(forward_demodulation,[],[f2237,f79])).
% 4.40/0.96  fof(f2237,plain,(
% 4.40/0.96    sK1 != k5_xboole_0(sK1,k1_xboole_0) | spl4_93),
% 4.40/0.96    inference(avatar_component_clause,[],[f2236])).
% 4.40/0.96  fof(f2236,plain,(
% 4.40/0.96    spl4_93 <=> sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 4.40/0.96  fof(f2844,plain,(
% 4.40/0.96    spl4_7 | ~spl4_3 | ~spl4_5),
% 4.40/0.96    inference(avatar_split_clause,[],[f2843,f88,f78,f127])).
% 4.40/0.96  fof(f88,plain,(
% 4.40/0.96    spl4_5 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.40/0.96  fof(f2843,plain,(
% 4.40/0.96    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl4_3 | ~spl4_5)),
% 4.40/0.96    inference(forward_demodulation,[],[f90,f79])).
% 4.40/0.96  fof(f90,plain,(
% 4.40/0.96    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl4_5),
% 4.40/0.96    inference(avatar_component_clause,[],[f88])).
% 4.40/0.96  fof(f2839,plain,(
% 4.40/0.96    ~spl4_8 | spl4_1 | ~spl4_3),
% 4.40/0.96    inference(avatar_split_clause,[],[f2838,f78,f69,f132])).
% 4.40/0.96  fof(f69,plain,(
% 4.40/0.96    spl4_1 <=> sK1 = k1_tarski(sK0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.40/0.96  fof(f2838,plain,(
% 4.40/0.96    k1_xboole_0 != k1_tarski(sK0) | (spl4_1 | ~spl4_3)),
% 4.40/0.96    inference(forward_demodulation,[],[f71,f79])).
% 4.40/0.96  fof(f71,plain,(
% 4.40/0.96    sK1 != k1_tarski(sK0) | spl4_1),
% 4.40/0.96    inference(avatar_component_clause,[],[f69])).
% 4.40/0.96  fof(f2792,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k1_tarski(sK0)) | k1_xboole_0 != sK1 | k3_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK0))) | k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f2769,plain,(
% 4.40/0.96    sK1 != k5_xboole_0(sK1,sK2) | k5_xboole_0(sK2,sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | k3_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | k1_xboole_0 != k4_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) != k5_xboole_0(sK2,k1_xboole_0) | k1_xboole_0 != k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) | k3_xboole_0(sK1,sK2) != k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f2728,plain,(
% 4.40/0.96    spl4_112 | ~spl4_49 | ~spl4_106),
% 4.40/0.96    inference(avatar_split_clause,[],[f2702,f2654,f710,f2725])).
% 4.40/0.96  fof(f710,plain,(
% 4.40/0.96    spl4_49 <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 4.40/0.96  fof(f2654,plain,(
% 4.40/0.96    spl4_106 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 4.40/0.96  fof(f2702,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | (~spl4_49 | ~spl4_106)),
% 4.40/0.96    inference(backward_demodulation,[],[f712,f2656])).
% 4.40/0.96  fof(f2656,plain,(
% 4.40/0.96    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl4_106),
% 4.40/0.96    inference(avatar_component_clause,[],[f2654])).
% 4.40/0.96  fof(f712,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl4_49),
% 4.40/0.96    inference(avatar_component_clause,[],[f710])).
% 4.40/0.96  fof(f2657,plain,(
% 4.40/0.96    spl4_106 | ~spl4_13 | ~spl4_78),
% 4.40/0.96    inference(avatar_split_clause,[],[f2625,f1960,f188,f2654])).
% 4.40/0.96  fof(f188,plain,(
% 4.40/0.96    spl4_13 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 4.40/0.96  fof(f1960,plain,(
% 4.40/0.96    spl4_78 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 4.40/0.96  fof(f2625,plain,(
% 4.40/0.96    k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl4_13 | ~spl4_78)),
% 4.40/0.96    inference(backward_demodulation,[],[f190,f1962])).
% 4.40/0.96  fof(f1962,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl4_78),
% 4.40/0.96    inference(avatar_component_clause,[],[f1960])).
% 4.40/0.96  fof(f190,plain,(
% 4.40/0.96    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl4_13),
% 4.40/0.96    inference(avatar_component_clause,[],[f188])).
% 4.40/0.96  fof(f2317,plain,(
% 4.40/0.96    spl4_78 | ~spl4_1 | ~spl4_36 | spl4_77),
% 4.40/0.96    inference(avatar_split_clause,[],[f2316,f1956,f562,f69,f1960])).
% 4.40/0.96  fof(f562,plain,(
% 4.40/0.96    spl4_36 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 4.40/0.96  fof(f1956,plain,(
% 4.40/0.96    spl4_77 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 4.40/0.96  fof(f2316,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | (~spl4_1 | ~spl4_36 | spl4_77)),
% 4.40/0.96    inference(subsumption_resolution,[],[f2288,f1957])).
% 4.40/0.96  fof(f1957,plain,(
% 4.40/0.96    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl4_77),
% 4.40/0.96    inference(avatar_component_clause,[],[f1956])).
% 4.40/0.96  fof(f2288,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl4_1 | ~spl4_36)),
% 4.40/0.96    inference(superposition,[],[f564,f476])).
% 4.40/0.96  fof(f476,plain,(
% 4.40/0.96    ( ! [X3] : (sK1 = k4_xboole_0(sK1,X3) | k1_xboole_0 = k4_xboole_0(sK1,X3)) ) | ~spl4_1),
% 4.40/0.96    inference(resolution,[],[f432,f57])).
% 4.40/0.96  fof(f57,plain,(
% 4.40/0.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.40/0.96    inference(cnf_transformation,[],[f7])).
% 4.40/0.96  fof(f7,axiom,(
% 4.40/0.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.40/0.96  fof(f432,plain,(
% 4.40/0.96    ( ! [X1] : (~r1_tarski(X1,sK1) | k1_xboole_0 = X1 | sK1 = X1) ) | ~spl4_1),
% 4.40/0.96    inference(superposition,[],[f43,f70])).
% 4.40/0.96  fof(f70,plain,(
% 4.40/0.96    sK1 = k1_tarski(sK0) | ~spl4_1),
% 4.40/0.96    inference(avatar_component_clause,[],[f69])).
% 4.40/0.96  fof(f564,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) | ~spl4_36),
% 4.40/0.96    inference(avatar_component_clause,[],[f562])).
% 4.40/0.96  fof(f2202,plain,(
% 4.40/0.96    spl4_33 | ~spl4_13),
% 4.40/0.96    inference(avatar_split_clause,[],[f2196,f188,f506])).
% 4.40/0.96  fof(f506,plain,(
% 4.40/0.96    spl4_33 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 4.40/0.96  fof(f2196,plain,(
% 4.40/0.96    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | ~spl4_13),
% 4.40/0.96    inference(superposition,[],[f487,f190])).
% 4.40/0.96  fof(f2199,plain,(
% 4.40/0.96    spl4_36 | ~spl4_13),
% 4.40/0.96    inference(avatar_split_clause,[],[f2198,f188,f562])).
% 4.40/0.96  fof(f2198,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) | ~spl4_13),
% 4.40/0.96    inference(forward_demodulation,[],[f2178,f62])).
% 4.40/0.96  fof(f62,plain,(
% 4.40/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.40/0.96    inference(cnf_transformation,[],[f5])).
% 4.40/0.96  fof(f5,axiom,(
% 4.40/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.40/0.96  fof(f2178,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl4_13),
% 4.40/0.96    inference(superposition,[],[f168,f190])).
% 4.40/0.96  fof(f2161,plain,(
% 4.40/0.96    k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | sK2 != k5_xboole_0(sK1,k1_xboole_0) | sK1 = sK2),
% 4.40/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.40/0.96  fof(f2158,plain,(
% 4.40/0.96    spl4_92 | ~spl4_87),
% 4.40/0.96    inference(avatar_split_clause,[],[f2124,f2078,f2155])).
% 4.40/0.96  fof(f2124,plain,(
% 4.40/0.96    sK2 = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_87),
% 4.40/0.96    inference(superposition,[],[f487,f2080])).
% 4.40/0.96  fof(f2080,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK1,sK2) | ~spl4_87),
% 4.40/0.96    inference(avatar_component_clause,[],[f2078])).
% 4.40/0.96  fof(f2086,plain,(
% 4.40/0.96    spl4_88 | spl4_87 | ~spl4_1 | ~spl4_80),
% 4.40/0.96    inference(avatar_split_clause,[],[f2073,f1980,f69,f2078,f2083])).
% 4.40/0.96  fof(f2083,plain,(
% 4.40/0.96    spl4_88 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 4.40/0.96  fof(f1980,plain,(
% 4.40/0.96    spl4_80 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 4.40/0.96  fof(f2073,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK1,sK2) | sK1 = k5_xboole_0(sK1,sK2) | (~spl4_1 | ~spl4_80)),
% 4.40/0.96    inference(resolution,[],[f2055,f432])).
% 4.40/0.96  fof(f2055,plain,(
% 4.40/0.96    ( ! [X0] : (r1_tarski(k5_xboole_0(sK1,sK2),X0)) ) | ~spl4_80),
% 4.40/0.96    inference(resolution,[],[f2040,f55])).
% 4.40/0.96  fof(f2040,plain,(
% 4.40/0.96    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,sK2))) ) | ~spl4_80),
% 4.40/0.96    inference(subsumption_resolution,[],[f2023,f397])).
% 4.40/0.96  fof(f2023,plain,(
% 4.40/0.96    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k5_xboole_0(sK1,sK2))) ) | ~spl4_80),
% 4.40/0.96    inference(duplicate_literal_removal,[],[f2002])).
% 4.40/0.96  fof(f2002,plain,(
% 4.40/0.96    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k5_xboole_0(sK1,sK2))) ) | ~spl4_80),
% 4.40/0.96    inference(superposition,[],[f60,f1982])).
% 4.40/0.96  fof(f1982,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) | ~spl4_80),
% 4.40/0.96    inference(avatar_component_clause,[],[f1980])).
% 4.40/0.96  fof(f1983,plain,(
% 4.40/0.96    spl4_80 | ~spl4_36 | ~spl4_77),
% 4.40/0.96    inference(avatar_split_clause,[],[f1969,f1956,f562,f1980])).
% 4.40/0.96  fof(f1969,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) | (~spl4_36 | ~spl4_77)),
% 4.40/0.96    inference(backward_demodulation,[],[f564,f1958])).
% 4.40/0.96  fof(f1958,plain,(
% 4.40/0.96    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl4_77),
% 4.40/0.96    inference(avatar_component_clause,[],[f1956])).
% 4.40/0.96  fof(f1780,plain,(
% 4.40/0.96    spl4_52 | ~spl4_49),
% 4.40/0.96    inference(avatar_split_clause,[],[f1771,f710,f768])).
% 4.40/0.96  fof(f768,plain,(
% 4.40/0.96    spl4_52 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK2,k1_xboole_0)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 4.40/0.96  fof(f1771,plain,(
% 4.40/0.96    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK2,k1_xboole_0) | ~spl4_49),
% 4.40/0.96    inference(superposition,[],[f487,f712])).
% 4.40/0.96  fof(f1744,plain,(
% 4.40/0.96    spl4_45 | ~spl4_14),
% 4.40/0.96    inference(avatar_split_clause,[],[f1730,f241,f678])).
% 4.40/0.96  fof(f678,plain,(
% 4.40/0.96    spl4_45 <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 4.40/0.96  fof(f241,plain,(
% 4.40/0.96    spl4_14 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 4.40/0.96  fof(f1730,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) | ~spl4_14),
% 4.40/0.96    inference(forward_demodulation,[],[f1729,f62])).
% 4.40/0.96  fof(f1729,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | ~spl4_14),
% 4.40/0.96    inference(forward_demodulation,[],[f1707,f47])).
% 4.40/0.96  fof(f1707,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK1,sK2))) | ~spl4_14),
% 4.40/0.96    inference(superposition,[],[f168,f243])).
% 4.40/0.96  fof(f243,plain,(
% 4.40/0.96    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl4_14),
% 4.40/0.96    inference(avatar_component_clause,[],[f241])).
% 4.40/0.96  fof(f1738,plain,(
% 4.40/0.96    spl4_70 | ~spl4_14),
% 4.40/0.96    inference(avatar_split_clause,[],[f1725,f241,f1735])).
% 4.40/0.96  fof(f1735,plain,(
% 4.40/0.96    spl4_70 <=> k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 4.40/0.96  fof(f1725,plain,(
% 4.40/0.96    k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl4_14),
% 4.40/0.96    inference(superposition,[],[f487,f243])).
% 4.40/0.96  fof(f1733,plain,(
% 4.40/0.96    spl4_49 | ~spl4_14),
% 4.40/0.96    inference(avatar_split_clause,[],[f1695,f241,f710])).
% 4.40/0.96  fof(f1695,plain,(
% 4.40/0.96    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl4_14),
% 4.40/0.96    inference(superposition,[],[f168,f243])).
% 4.40/0.96  fof(f1369,plain,(
% 4.40/0.96    spl4_63 | ~spl4_59),
% 4.40/0.96    inference(avatar_split_clause,[],[f1358,f1200,f1366])).
% 4.40/0.96  fof(f1200,plain,(
% 4.40/0.96    spl4_59 <=> k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 4.40/0.96  fof(f1358,plain,(
% 4.40/0.96    r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK1) | ~spl4_59),
% 4.40/0.96    inference(superposition,[],[f57,f1202])).
% 4.40/0.96  fof(f1202,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2) | ~spl4_59),
% 4.40/0.96    inference(avatar_component_clause,[],[f1200])).
% 4.40/0.96  fof(f1268,plain,(
% 4.40/0.96    spl4_14 | ~spl4_12),
% 4.40/0.96    inference(avatar_split_clause,[],[f643,f158,f241])).
% 4.40/0.96  fof(f158,plain,(
% 4.40/0.96    spl4_12 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 4.40/0.96  fof(f643,plain,(
% 4.40/0.96    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl4_12),
% 4.40/0.96    inference(superposition,[],[f180,f160])).
% 4.40/0.96  fof(f160,plain,(
% 4.40/0.96    sK1 = k2_xboole_0(sK1,sK2) | ~spl4_12),
% 4.40/0.96    inference(avatar_component_clause,[],[f158])).
% 4.40/0.96  fof(f1204,plain,(
% 4.40/0.96    spl4_59 | ~spl4_41),
% 4.40/0.96    inference(avatar_split_clause,[],[f1183,f606,f1200])).
% 4.40/0.96  fof(f606,plain,(
% 4.40/0.96    spl4_41 <=> k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 4.40/0.96  fof(f1183,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK2) | ~spl4_41),
% 4.40/0.96    inference(superposition,[],[f62,f608])).
% 4.40/0.96  fof(f608,plain,(
% 4.40/0.96    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl4_41),
% 4.40/0.96    inference(avatar_component_clause,[],[f606])).
% 4.40/0.96  fof(f631,plain,(
% 4.40/0.96    spl4_42 | ~spl4_33),
% 4.40/0.96    inference(avatar_split_clause,[],[f617,f506,f627])).
% 4.40/0.96  fof(f627,plain,(
% 4.40/0.96    spl4_42 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 4.40/0.96  fof(f617,plain,(
% 4.40/0.96    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl4_33),
% 4.40/0.96    inference(superposition,[],[f47,f508])).
% 4.40/0.96  fof(f508,plain,(
% 4.40/0.96    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | ~spl4_33),
% 4.40/0.96    inference(avatar_component_clause,[],[f506])).
% 4.40/0.96  fof(f439,plain,(
% 4.40/0.96    spl4_13 | ~spl4_12),
% 4.40/0.96    inference(avatar_split_clause,[],[f437,f158,f188])).
% 4.40/0.96  fof(f437,plain,(
% 4.40/0.96    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl4_12),
% 4.40/0.96    inference(superposition,[],[f49,f160])).
% 4.40/0.96  fof(f161,plain,(
% 4.40/0.96    spl4_12 | ~spl4_1 | ~spl4_5),
% 4.40/0.96    inference(avatar_split_clause,[],[f156,f88,f69,f158])).
% 4.40/0.96  fof(f156,plain,(
% 4.40/0.96    sK1 = k2_xboole_0(sK1,sK2) | (~spl4_1 | ~spl4_5)),
% 4.40/0.96    inference(forward_demodulation,[],[f90,f70])).
% 4.40/0.96  fof(f145,plain,(
% 4.40/0.96    ~spl4_9 | ~spl4_1 | spl4_4),
% 4.40/0.96    inference(avatar_split_clause,[],[f137,f82,f69,f142])).
% 4.40/0.96  fof(f142,plain,(
% 4.40/0.96    spl4_9 <=> sK1 = sK2),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 4.40/0.96  fof(f137,plain,(
% 4.40/0.96    sK1 != sK2 | (~spl4_1 | spl4_4)),
% 4.40/0.96    inference(backward_demodulation,[],[f84,f70])).
% 4.40/0.96  fof(f136,plain,(
% 4.40/0.96    spl4_1 | spl4_3 | ~spl4_6),
% 4.40/0.96    inference(avatar_split_clause,[],[f118,f95,f78,f69])).
% 4.40/0.96  fof(f95,plain,(
% 4.40/0.96    spl4_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 4.40/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 4.40/0.96  fof(f118,plain,(
% 4.40/0.96    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0) | ~spl4_6),
% 4.40/0.96    inference(resolution,[],[f43,f97])).
% 4.40/0.96  fof(f97,plain,(
% 4.40/0.96    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_6),
% 4.40/0.96    inference(avatar_component_clause,[],[f95])).
% 4.40/0.96  fof(f98,plain,(
% 4.40/0.96    spl4_6 | ~spl4_5),
% 4.40/0.96    inference(avatar_split_clause,[],[f92,f88,f95])).
% 4.40/0.96  fof(f92,plain,(
% 4.40/0.96    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_5),
% 4.40/0.96    inference(superposition,[],[f51,f90])).
% 4.40/0.96  fof(f51,plain,(
% 4.40/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.40/0.96    inference(cnf_transformation,[],[f8])).
% 4.40/0.96  fof(f8,axiom,(
% 4.40/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.40/0.96  fof(f91,plain,(
% 4.40/0.96    spl4_5),
% 4.40/0.96    inference(avatar_split_clause,[],[f39,f88])).
% 4.40/0.96  fof(f39,plain,(
% 4.40/0.96    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 4.40/0.96    inference(cnf_transformation,[],[f31])).
% 4.40/0.96  fof(f31,plain,(
% 4.40/0.96    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 4.40/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).
% 4.40/0.96  fof(f30,plain,(
% 4.40/0.96    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 4.40/0.96    introduced(choice_axiom,[])).
% 4.40/0.96  fof(f25,plain,(
% 4.40/0.96    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.40/0.96    inference(ennf_transformation,[],[f22])).
% 4.40/0.96  fof(f22,negated_conjecture,(
% 4.40/0.96    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.40/0.96    inference(negated_conjecture,[],[f21])).
% 4.40/0.96  fof(f21,conjecture,(
% 4.40/0.96    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 4.40/0.96  fof(f86,plain,(
% 4.40/0.96    ~spl4_1 | ~spl4_4),
% 4.40/0.96    inference(avatar_split_clause,[],[f40,f82,f69])).
% 4.40/0.96  fof(f40,plain,(
% 4.40/0.96    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 4.40/0.96    inference(cnf_transformation,[],[f31])).
% 4.40/0.96  fof(f85,plain,(
% 4.40/0.96    ~spl4_3 | ~spl4_4),
% 4.40/0.96    inference(avatar_split_clause,[],[f41,f82,f78])).
% 4.40/0.96  fof(f41,plain,(
% 4.40/0.96    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 4.40/0.96    inference(cnf_transformation,[],[f31])).
% 4.40/0.96  fof(f76,plain,(
% 4.40/0.96    ~spl4_1 | ~spl4_2),
% 4.40/0.96    inference(avatar_split_clause,[],[f42,f73,f69])).
% 4.40/0.96  fof(f42,plain,(
% 4.40/0.96    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 4.40/0.96    inference(cnf_transformation,[],[f31])).
% 4.40/0.97  % (411)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.40/0.97  % SZS output end Proof for theBenchmark
% 4.40/0.97  % (32733)------------------------------
% 4.40/0.97  % (32733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.97  % (32733)Termination reason: Refutation
% 4.40/0.97  
% 4.40/0.97  % (32733)Memory used [KB]: 9338
% 4.40/0.97  % (32733)Time elapsed: 0.434 s
% 4.40/0.97  % (32733)------------------------------
% 4.40/0.97  % (32733)------------------------------
% 4.40/0.97  % (32687)Success in time 0.6 s
%------------------------------------------------------------------------------
