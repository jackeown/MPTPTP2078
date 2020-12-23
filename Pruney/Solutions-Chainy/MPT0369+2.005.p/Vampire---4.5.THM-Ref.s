%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 145 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 333 expanded)
%              Number of equality atoms :   43 (  77 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f129,f132,f170,f317,f450,f465,f493,f494])).

fof(f494,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f493,plain,
    ( spl3_48
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f485,f462,f487])).

fof(f487,plain,
    ( spl3_48
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f462,plain,
    ( spl3_47
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f485,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_47 ),
    inference(superposition,[],[f39,f464])).

fof(f464,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f462])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f465,plain,
    ( spl3_47
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f460,f447,f462])).

fof(f447,plain,
    ( spl3_46
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f460,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_46 ),
    inference(resolution,[],[f449,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f449,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f447])).

fof(f450,plain,
    ( spl3_46
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f445,f64,f447])).

fof(f64,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f445,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f400,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

% (26651)Refutation not found, incomplete strategy% (26651)------------------------------
% (26651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26651)Termination reason: Refutation not found, incomplete strategy

% (26651)Memory used [KB]: 10746
% (26651)Time elapsed: 0.092 s
% (26651)------------------------------
% (26651)------------------------------
fof(f400,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f185,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f55,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

% (26646)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f185,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | r1_tarski(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(global_subsumption,[],[f32,f183])).

% (26658)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f183,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | r1_tarski(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f49,f143])).

fof(f143,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f141,f55])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f317,plain,
    ( spl3_32
    | spl3_3
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f308,f167,f126,f69,f314])).

fof(f314,plain,
    ( spl3_32
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f69,plain,
    ( spl3_3
  <=> r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( spl3_13
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f167,plain,
    ( spl3_17
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f308,plain,
    ( r2_hidden(sK2,k3_subset_1(sK0,sK1))
    | r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(superposition,[],[f159,f169])).

fof(f169,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f159,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k5_xboole_0(sK0,X0))
        | r2_hidden(sK2,X0) )
    | ~ spl3_13 ),
    inference(resolution,[],[f53,f128])).

fof(f128,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f170,plain,
    ( spl3_17
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f163,f64,f167])).

fof(f163,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f66])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f132,plain,
    ( spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f131,f106,f59])).

fof(f59,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,
    ( spl3_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f131,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_10 ),
    inference(resolution,[],[f107,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f107,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f129,plain,
    ( spl3_10
    | spl3_13
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f79,f126,f106])).

fof(f79,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f44,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f82,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f79])).

fof(f27,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f77,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f74,plain,
    ( spl3_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f28,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (26636)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (26645)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (26633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26629)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (26637)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (26645)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 1.28/0.52  % (26653)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.53  % (26630)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (26651)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (26641)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (26629)Refutation not found, incomplete strategy% (26629)------------------------------
% 1.28/0.53  % (26629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (26629)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (26629)Memory used [KB]: 1663
% 1.28/0.53  % (26629)Time elapsed: 0.122 s
% 1.28/0.53  % (26629)------------------------------
% 1.28/0.53  % (26629)------------------------------
% 1.28/0.53  % (26631)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (26637)Refutation not found, incomplete strategy% (26637)------------------------------
% 1.28/0.53  % (26637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (26637)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (26637)Memory used [KB]: 10746
% 1.28/0.53  % (26637)Time elapsed: 0.114 s
% 1.28/0.53  % (26637)------------------------------
% 1.28/0.53  % (26637)------------------------------
% 1.28/0.53  % (26644)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (26632)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (26635)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f495,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f129,f132,f170,f317,f450,f465,f493,f494])).
% 1.28/0.53  fof(f494,plain,(
% 1.28/0.53    sK1 != k3_xboole_0(sK0,sK1) | r2_hidden(sK2,sK1) | ~r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 1.28/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.53  fof(f493,plain,(
% 1.28/0.53    spl3_48 | ~spl3_47),
% 1.28/0.53    inference(avatar_split_clause,[],[f485,f462,f487])).
% 1.28/0.53  fof(f487,plain,(
% 1.28/0.53    spl3_48 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.28/0.53  fof(f462,plain,(
% 1.28/0.53    spl3_47 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.28/0.53  fof(f485,plain,(
% 1.28/0.53    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_47),
% 1.28/0.53    inference(superposition,[],[f39,f464])).
% 1.28/0.53  fof(f464,plain,(
% 1.28/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_47),
% 1.28/0.53    inference(avatar_component_clause,[],[f462])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.28/0.53  fof(f465,plain,(
% 1.28/0.53    spl3_47 | ~spl3_46),
% 1.28/0.53    inference(avatar_split_clause,[],[f460,f447,f462])).
% 1.28/0.53  fof(f447,plain,(
% 1.28/0.53    spl3_46 <=> r1_tarski(sK1,sK0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.28/0.53  fof(f460,plain,(
% 1.28/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_46),
% 1.28/0.53    inference(resolution,[],[f449,f45])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.28/0.53  fof(f449,plain,(
% 1.28/0.53    r1_tarski(sK1,sK0) | ~spl3_46),
% 1.28/0.53    inference(avatar_component_clause,[],[f447])).
% 1.28/0.53  fof(f450,plain,(
% 1.28/0.53    spl3_46 | ~spl3_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f445,f64,f447])).
% 1.28/0.53  fof(f64,plain,(
% 1.28/0.53    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.28/0.53  fof(f445,plain,(
% 1.28/0.53    r1_tarski(sK1,sK0) | ~spl3_2),
% 1.28/0.53    inference(resolution,[],[f400,f66])).
% 1.28/0.53  fof(f66,plain,(
% 1.28/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f64])).
% 1.28/0.53  % (26651)Refutation not found, incomplete strategy% (26651)------------------------------
% 1.28/0.53  % (26651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (26651)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (26651)Memory used [KB]: 10746
% 1.28/0.53  % (26651)Time elapsed: 0.092 s
% 1.28/0.53  % (26651)------------------------------
% 1.28/0.53  % (26651)------------------------------
% 1.28/0.53  fof(f400,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(resolution,[],[f185,f83])).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.28/0.53    inference(forward_demodulation,[],[f56,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.28/0.53    inference(definition_unfolding,[],[f34,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f37,f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f13])).
% 1.28/0.53  fof(f13,axiom,(
% 1.28/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.28/0.53    inference(definition_unfolding,[],[f36,f54])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.28/0.53  % (26646)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.53  fof(f185,plain,(
% 1.28/0.53    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X2)) | r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.28/0.53    inference(global_subsumption,[],[f32,f183])).
% 1.28/0.53  % (26658)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.53  fof(f183,plain,(
% 1.28/0.53    ( ! [X2,X3] : (~r1_xboole_0(X3,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(X2)) | r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.28/0.53    inference(superposition,[],[f49,f143])).
% 1.28/0.53  fof(f143,plain,(
% 1.28/0.53    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f141,f55])).
% 1.28/0.53  fof(f141,plain,(
% 1.28/0.53    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 1.28/0.53    inference(resolution,[],[f47,f35])).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,axiom,(
% 1.28/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f12])).
% 1.28/0.54  fof(f12,axiom,(
% 1.28/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f14])).
% 1.28/0.54  fof(f14,axiom,(
% 1.28/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.28/0.54  fof(f317,plain,(
% 1.28/0.54    spl3_32 | spl3_3 | ~spl3_13 | ~spl3_17),
% 1.28/0.54    inference(avatar_split_clause,[],[f308,f167,f126,f69,f314])).
% 1.28/0.54  fof(f314,plain,(
% 1.28/0.54    spl3_32 <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.28/0.54  fof(f69,plain,(
% 1.28/0.54    spl3_3 <=> r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.28/0.54  fof(f126,plain,(
% 1.28/0.54    spl3_13 <=> r2_hidden(sK2,sK0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.28/0.54  fof(f167,plain,(
% 1.28/0.54    spl3_17 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.28/0.54  fof(f308,plain,(
% 1.28/0.54    r2_hidden(sK2,k3_subset_1(sK0,sK1)) | r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | (~spl3_13 | ~spl3_17)),
% 1.28/0.54    inference(superposition,[],[f159,f169])).
% 1.28/0.54  fof(f169,plain,(
% 1.28/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_17),
% 1.28/0.54    inference(avatar_component_clause,[],[f167])).
% 1.28/0.54  fof(f159,plain,(
% 1.28/0.54    ( ! [X0] : (r2_hidden(sK2,k5_xboole_0(sK0,X0)) | r2_hidden(sK2,X0)) ) | ~spl3_13),
% 1.28/0.54    inference(resolution,[],[f53,f128])).
% 1.28/0.54  fof(f128,plain,(
% 1.28/0.54    r2_hidden(sK2,sK0) | ~spl3_13),
% 1.28/0.54    inference(avatar_component_clause,[],[f126])).
% 1.28/0.54  fof(f53,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.28/0.54    inference(ennf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.28/0.54  fof(f170,plain,(
% 1.28/0.54    spl3_17 | ~spl3_2),
% 1.28/0.54    inference(avatar_split_clause,[],[f163,f64,f167])).
% 1.28/0.54  fof(f163,plain,(
% 1.28/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 1.28/0.54    inference(resolution,[],[f57,f66])).
% 1.28/0.54  fof(f57,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.28/0.54    inference(definition_unfolding,[],[f46,f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.28/0.54  fof(f132,plain,(
% 1.28/0.54    spl3_1 | ~spl3_10),
% 1.28/0.54    inference(avatar_split_clause,[],[f131,f106,f59])).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    spl3_1 <=> k1_xboole_0 = sK0),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.28/0.54  fof(f106,plain,(
% 1.28/0.54    spl3_10 <=> v1_xboole_0(sK0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.28/0.54  fof(f131,plain,(
% 1.28/0.54    k1_xboole_0 = sK0 | ~spl3_10),
% 1.28/0.54    inference(resolution,[],[f107,f38])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    v1_xboole_0(sK0) | ~spl3_10),
% 1.28/0.54    inference(avatar_component_clause,[],[f106])).
% 1.28/0.54  fof(f129,plain,(
% 1.28/0.54    spl3_10 | spl3_13 | ~spl3_5),
% 1.28/0.54    inference(avatar_split_clause,[],[f119,f79,f126,f106])).
% 1.28/0.54  fof(f79,plain,(
% 1.28/0.54    spl3_5 <=> m1_subset_1(sK2,sK0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.28/0.54  fof(f119,plain,(
% 1.28/0.54    r2_hidden(sK2,sK0) | v1_xboole_0(sK0) | ~spl3_5),
% 1.28/0.54    inference(resolution,[],[f44,f81])).
% 1.28/0.54  fof(f81,plain,(
% 1.28/0.54    m1_subset_1(sK2,sK0) | ~spl3_5),
% 1.28/0.54    inference(avatar_component_clause,[],[f79])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.28/0.54  fof(f82,plain,(
% 1.28/0.54    spl3_5),
% 1.28/0.54    inference(avatar_split_clause,[],[f27,f79])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    m1_subset_1(sK2,sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.28/0.54    inference(flattening,[],[f18])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.28/0.54    inference(ennf_transformation,[],[f17])).
% 1.28/0.54  fof(f17,negated_conjecture,(
% 1.28/0.54    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.28/0.54    inference(negated_conjecture,[],[f16])).
% 1.28/0.54  fof(f16,conjecture,(
% 1.28/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.28/0.54  fof(f77,plain,(
% 1.28/0.54    ~spl3_4),
% 1.28/0.54    inference(avatar_split_clause,[],[f28,f74])).
% 1.28/0.54  fof(f74,plain,(
% 1.28/0.54    spl3_4 <=> r2_hidden(sK2,sK1)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ~r2_hidden(sK2,sK1)),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f72,plain,(
% 1.28/0.54    ~spl3_3),
% 1.28/0.54    inference(avatar_split_clause,[],[f29,f69])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f67,plain,(
% 1.28/0.54    spl3_2),
% 1.28/0.54    inference(avatar_split_clause,[],[f30,f64])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    ~spl3_1),
% 1.28/0.54    inference(avatar_split_clause,[],[f31,f59])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    k1_xboole_0 != sK0),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (26645)------------------------------
% 1.28/0.54  % (26645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (26645)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (26645)Memory used [KB]: 11001
% 1.28/0.54  % (26645)Time elapsed: 0.115 s
% 1.28/0.54  % (26645)------------------------------
% 1.28/0.54  % (26645)------------------------------
% 1.28/0.54  % (26634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (26631)Refutation not found, incomplete strategy% (26631)------------------------------
% 1.28/0.54  % (26631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (26631)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (26631)Memory used [KB]: 10746
% 1.28/0.54  % (26631)Time elapsed: 0.124 s
% 1.28/0.54  % (26631)------------------------------
% 1.28/0.54  % (26631)------------------------------
% 1.28/0.54  % (26657)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.54  % (26628)Success in time 0.177 s
%------------------------------------------------------------------------------
