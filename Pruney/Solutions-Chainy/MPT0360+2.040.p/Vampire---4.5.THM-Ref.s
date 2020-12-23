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
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 349 expanded)
%              Number of leaves         :   18 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 (1083 expanded)
%              Number of equality atoms :   42 ( 223 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f846,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f566,f571,f832,f844])).

fof(f844,plain,
    ( ~ spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f843,f266,f314])).

fof(f314,plain,
    ( spl5_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f266,plain,
    ( spl5_8
  <=> sK1 = k3_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f843,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f842,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f842,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f457,f268])).

fof(f268,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f266])).

fof(f457,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | k1_xboole_0 = k3_subset_1(sK1,sK1) ),
    inference(superposition,[],[f253,f159])).

fof(f159,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(unit_resulting_resolution,[],[f124,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f124,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f42,f98])).

fof(f98,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,sK2)
      | ~ r1_tarski(X1,k3_subset_1(sK0,sK2)) ) ),
    inference(superposition,[],[f71,f78])).

fof(f78,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f64,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f253,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f52,f137])).

fof(f137,plain,(
    ! [X2] :
      ( sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2)))
      | ~ m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f89,f67])).

fof(f89,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f75,f69])).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f39,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f832,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f824,f42])).

fof(f824,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f633,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f633,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f316,f491,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f491,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f160,f316,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f42,f124,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f316,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f314])).

fof(f571,plain,
    ( ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f325,f266,f262])).

fof(f262,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f325,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f137,f162])).

fof(f162,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f125,f69])).

fof(f125,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f40,f98])).

fof(f40,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f566,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f563,f564])).

fof(f564,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f516,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f516,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f471,f73])).

fof(f471,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f264,f276,f47])).

fof(f276,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f117,f264,f49])).

fof(f117,plain,(
    v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f40,f93,f50])).

fof(f93,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f75,f78])).

fof(f264,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f262])).

fof(f563,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f516,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (2408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.49  % (2416)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (2394)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (2394)Refutation not found, incomplete strategy% (2394)------------------------------
% 0.20/0.54  % (2394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2394)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2394)Memory used [KB]: 1663
% 0.20/0.54  % (2394)Time elapsed: 0.118 s
% 0.20/0.54  % (2394)------------------------------
% 0.20/0.54  % (2394)------------------------------
% 0.20/0.55  % (2397)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (2410)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (2398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (2407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (2399)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (2395)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (2406)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (2417)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (2409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (2414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (2419)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (2421)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (2422)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (2418)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (2413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (2411)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (2396)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (2400)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.57  % (2417)Refutation not found, incomplete strategy% (2417)------------------------------
% 0.20/0.57  % (2417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (2417)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (2417)Memory used [KB]: 10746
% 0.20/0.57  % (2417)Time elapsed: 0.122 s
% 0.20/0.57  % (2417)------------------------------
% 0.20/0.57  % (2417)------------------------------
% 0.20/0.57  % (2405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.58  % (2405)Refutation not found, incomplete strategy% (2405)------------------------------
% 0.20/0.58  % (2405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (2405)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (2405)Memory used [KB]: 10618
% 0.20/0.58  % (2405)Time elapsed: 0.148 s
% 0.20/0.58  % (2405)------------------------------
% 0.20/0.58  % (2405)------------------------------
% 0.20/0.58  % (2406)Refutation not found, incomplete strategy% (2406)------------------------------
% 0.20/0.58  % (2406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (2406)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (2406)Memory used [KB]: 10618
% 0.20/0.58  % (2406)Time elapsed: 0.180 s
% 0.20/0.58  % (2406)------------------------------
% 0.20/0.58  % (2406)------------------------------
% 0.20/0.58  % (2403)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.58  % (2423)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (2424)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.59  % (2401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.59  % (2403)Refutation not found, incomplete strategy% (2403)------------------------------
% 1.58/0.59  % (2403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (2403)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (2403)Memory used [KB]: 10746
% 1.58/0.59  % (2403)Time elapsed: 0.159 s
% 1.58/0.59  % (2403)------------------------------
% 1.58/0.59  % (2403)------------------------------
% 1.58/0.59  % (2415)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.60  % (2396)Refutation not found, incomplete strategy% (2396)------------------------------
% 1.58/0.60  % (2396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (2396)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (2396)Memory used [KB]: 10746
% 1.58/0.60  % (2396)Time elapsed: 0.175 s
% 1.58/0.60  % (2396)------------------------------
% 1.58/0.60  % (2396)------------------------------
% 1.58/0.60  % (2412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.89/0.61  % (2420)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.89/0.61  % (2412)Refutation not found, incomplete strategy% (2412)------------------------------
% 1.89/0.61  % (2412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (2412)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (2412)Memory used [KB]: 10618
% 1.89/0.61  % (2412)Time elapsed: 0.191 s
% 1.89/0.61  % (2412)------------------------------
% 1.89/0.61  % (2412)------------------------------
% 1.89/0.62  % (2404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.89/0.62  % (2404)Refutation not found, incomplete strategy% (2404)------------------------------
% 1.89/0.62  % (2404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (2404)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (2404)Memory used [KB]: 10618
% 1.89/0.62  % (2404)Time elapsed: 0.200 s
% 1.89/0.62  % (2404)------------------------------
% 1.89/0.62  % (2404)------------------------------
% 2.10/0.67  % (2421)Refutation found. Thanks to Tanya!
% 2.10/0.67  % SZS status Theorem for theBenchmark
% 2.10/0.67  % SZS output start Proof for theBenchmark
% 2.10/0.67  fof(f846,plain,(
% 2.10/0.67    $false),
% 2.10/0.67    inference(avatar_sat_refutation,[],[f566,f571,f832,f844])).
% 2.10/0.67  fof(f844,plain,(
% 2.10/0.67    ~spl5_11 | ~spl5_8),
% 2.10/0.67    inference(avatar_split_clause,[],[f843,f266,f314])).
% 2.10/0.67  fof(f314,plain,(
% 2.10/0.67    spl5_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.10/0.67  fof(f266,plain,(
% 2.10/0.67    spl5_8 <=> sK1 = k3_subset_1(sK1,sK1)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.10/0.67  fof(f843,plain,(
% 2.10/0.67    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl5_8),
% 2.10/0.67    inference(subsumption_resolution,[],[f842,f41])).
% 2.10/0.67  fof(f41,plain,(
% 2.10/0.67    k1_xboole_0 != sK1),
% 2.10/0.67    inference(cnf_transformation,[],[f27])).
% 2.10/0.67  fof(f27,plain,(
% 2.10/0.67    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).
% 2.10/0.67  fof(f26,plain,(
% 2.10/0.67    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f17,plain,(
% 2.10/0.67    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(flattening,[],[f16])).
% 2.10/0.67  fof(f16,plain,(
% 2.10/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f15])).
% 2.10/0.67  fof(f15,negated_conjecture,(
% 2.10/0.67    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.10/0.67    inference(negated_conjecture,[],[f14])).
% 2.10/0.67  fof(f14,conjecture,(
% 2.10/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 2.10/0.67  fof(f842,plain,(
% 2.10/0.67    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl5_8),
% 2.10/0.67    inference(forward_demodulation,[],[f457,f268])).
% 2.10/0.67  fof(f268,plain,(
% 2.10/0.67    sK1 = k3_subset_1(sK1,sK1) | ~spl5_8),
% 2.10/0.67    inference(avatar_component_clause,[],[f266])).
% 2.10/0.67  fof(f457,plain,(
% 2.10/0.67    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | k1_xboole_0 = k3_subset_1(sK1,sK1)),
% 2.10/0.67    inference(superposition,[],[f253,f159])).
% 2.10/0.67  fof(f159,plain,(
% 2.10/0.67    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2))),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f124,f69])).
% 2.10/0.67  fof(f69,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.10/0.67    inference(definition_unfolding,[],[f53,f45])).
% 2.10/0.67  fof(f45,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f2])).
% 2.10/0.67  fof(f2,axiom,(
% 2.10/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.10/0.67  fof(f53,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f29])).
% 2.10/0.67  fof(f29,plain,(
% 2.10/0.67    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.10/0.67    inference(nnf_transformation,[],[f8])).
% 2.10/0.67  fof(f8,axiom,(
% 2.10/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.10/0.67  fof(f124,plain,(
% 2.10/0.67    r1_xboole_0(k1_xboole_0,sK2)),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f42,f98])).
% 2.10/0.67  fof(f98,plain,(
% 2.10/0.67    ( ! [X1] : (r1_xboole_0(X1,sK2) | ~r1_tarski(X1,k3_subset_1(sK0,sK2))) )),
% 2.10/0.67    inference(superposition,[],[f71,f78])).
% 2.10/0.67  fof(f78,plain,(
% 2.10/0.67    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f38,f67])).
% 2.10/0.67  fof(f67,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(definition_unfolding,[],[f51,f45])).
% 2.10/0.67  fof(f51,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f21])).
% 2.10/0.67  fof(f21,plain,(
% 2.10/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f12])).
% 2.10/0.67  fof(f12,axiom,(
% 2.10/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.10/0.67  fof(f38,plain,(
% 2.10/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.10/0.67    inference(cnf_transformation,[],[f27])).
% 2.10/0.67  fof(f71,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.10/0.67    inference(definition_unfolding,[],[f64,f45])).
% 2.10/0.67  fof(f64,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f25])).
% 2.10/0.67  fof(f25,plain,(
% 2.10/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.10/0.67    inference(ennf_transformation,[],[f3])).
% 2.10/0.67  fof(f3,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.10/0.67  fof(f42,plain,(
% 2.10/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f4])).
% 2.10/0.67  fof(f4,axiom,(
% 2.10/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.10/0.67  fof(f253,plain,(
% 2.10/0.67    ( ! [X0] : (~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1)) )),
% 2.10/0.67    inference(duplicate_literal_removal,[],[f252])).
% 2.10/0.67  fof(f252,plain,(
% 2.10/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(sK1,sK1) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(sK1))) )),
% 2.10/0.67    inference(superposition,[],[f52,f137])).
% 2.10/0.67  fof(f137,plain,(
% 2.10/0.67    ( ! [X2] : (sK1 = k3_subset_1(sK1,k5_xboole_0(X2,k3_xboole_0(X2,sK2))) | ~m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,sK2)),k1_zfmisc_1(sK1))) )),
% 2.10/0.67    inference(superposition,[],[f89,f67])).
% 2.10/0.67  fof(f89,plain,(
% 2.10/0.67    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))))) )),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f75,f69])).
% 2.10/0.67  fof(f75,plain,(
% 2.10/0.67    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) )),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f39,f70])).
% 2.10/0.67  fof(f70,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(definition_unfolding,[],[f62,f45])).
% 2.10/0.67  fof(f62,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f24])).
% 2.10/0.67  fof(f24,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.10/0.67    inference(ennf_transformation,[],[f9])).
% 2.10/0.67  fof(f9,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.10/0.67  fof(f39,plain,(
% 2.10/0.67    r1_tarski(sK1,sK2)),
% 2.10/0.67    inference(cnf_transformation,[],[f27])).
% 2.10/0.67  fof(f52,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f22])).
% 2.10/0.67  fof(f22,plain,(
% 2.10/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f13])).
% 2.10/0.67  fof(f13,axiom,(
% 2.10/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.10/0.67  fof(f832,plain,(
% 2.10/0.67    spl5_11),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f831])).
% 2.10/0.67  fof(f831,plain,(
% 2.10/0.67    $false | spl5_11),
% 2.10/0.67    inference(subsumption_resolution,[],[f824,f42])).
% 2.10/0.67  fof(f824,plain,(
% 2.10/0.67    ~r1_tarski(k1_xboole_0,sK1) | spl5_11),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f633,f73])).
% 2.10/0.67  fof(f73,plain,(
% 2.10/0.67    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.10/0.67    inference(equality_resolution,[],[f59])).
% 2.10/0.67  fof(f59,plain,(
% 2.10/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.10/0.67    inference(cnf_transformation,[],[f37])).
% 2.10/0.67  fof(f37,plain,(
% 2.10/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.10/0.67  fof(f36,plain,(
% 2.10/0.67    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f35,plain,(
% 2.10/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.67    inference(rectify,[],[f34])).
% 2.10/0.67  fof(f34,plain,(
% 2.10/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.67    inference(nnf_transformation,[],[f10])).
% 2.10/0.67  fof(f10,axiom,(
% 2.10/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.10/0.67  fof(f633,plain,(
% 2.10/0.67    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_11),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f316,f491,f47])).
% 2.10/0.67  fof(f47,plain,(
% 2.10/0.67    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f28])).
% 2.10/0.67  fof(f28,plain,(
% 2.10/0.67    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.10/0.67    inference(nnf_transformation,[],[f18])).
% 2.10/0.67  fof(f18,plain,(
% 2.10/0.67    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f11])).
% 2.10/0.67  fof(f11,axiom,(
% 2.10/0.67    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.10/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.10/0.67  fof(f491,plain,(
% 2.10/0.67    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_11),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f160,f316,f49])).
% 2.10/0.67  fof(f49,plain,(
% 2.10/0.67    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f28])).
% 2.10/0.67  fof(f160,plain,(
% 2.10/0.67    v1_xboole_0(k1_xboole_0)),
% 2.10/0.67    inference(unit_resulting_resolution,[],[f42,f124,f50])).
% 2.10/0.67  fof(f50,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f20])).
% 2.10/0.69  fof(f20,plain,(
% 2.10/0.69    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.10/0.69    inference(flattening,[],[f19])).
% 2.10/0.69  fof(f19,plain,(
% 2.10/0.69    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.10/0.69    inference(ennf_transformation,[],[f6])).
% 2.10/0.69  fof(f6,axiom,(
% 2.10/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.10/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.10/0.69  fof(f316,plain,(
% 2.10/0.69    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_11),
% 2.10/0.69    inference(avatar_component_clause,[],[f314])).
% 2.10/0.69  fof(f571,plain,(
% 2.10/0.69    ~spl5_7 | spl5_8),
% 2.10/0.69    inference(avatar_split_clause,[],[f325,f266,f262])).
% 2.10/0.69  fof(f262,plain,(
% 2.10/0.69    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.10/0.69  fof(f325,plain,(
% 2.10/0.69    sK1 = k3_subset_1(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.10/0.69    inference(superposition,[],[f137,f162])).
% 2.10/0.69  fof(f162,plain,(
% 2.10/0.69    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f125,f69])).
% 2.10/0.69  fof(f125,plain,(
% 2.10/0.69    r1_xboole_0(sK1,sK2)),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f40,f98])).
% 2.10/0.69  fof(f40,plain,(
% 2.10/0.69    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.10/0.69    inference(cnf_transformation,[],[f27])).
% 2.10/0.69  fof(f566,plain,(
% 2.10/0.69    spl5_7),
% 2.10/0.69    inference(avatar_contradiction_clause,[],[f565])).
% 2.10/0.69  fof(f565,plain,(
% 2.10/0.69    $false | spl5_7),
% 2.10/0.69    inference(subsumption_resolution,[],[f563,f564])).
% 2.10/0.69  fof(f564,plain,(
% 2.10/0.69    ~r2_hidden(sK3(sK1,sK1),sK1) | spl5_7),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f516,f57])).
% 2.10/0.69  fof(f57,plain,(
% 2.10/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.10/0.69    inference(cnf_transformation,[],[f33])).
% 2.10/0.69  fof(f33,plain,(
% 2.10/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.10/0.69  fof(f32,plain,(
% 2.10/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.10/0.69    introduced(choice_axiom,[])).
% 2.10/0.69  fof(f31,plain,(
% 2.10/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.69    inference(rectify,[],[f30])).
% 2.10/0.69  fof(f30,plain,(
% 2.10/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.69    inference(nnf_transformation,[],[f23])).
% 2.10/0.69  fof(f23,plain,(
% 2.10/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.69    inference(ennf_transformation,[],[f1])).
% 2.10/0.69  fof(f1,axiom,(
% 2.10/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.10/0.69  fof(f516,plain,(
% 2.10/0.69    ~r1_tarski(sK1,sK1) | spl5_7),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f471,f73])).
% 2.10/0.69  fof(f471,plain,(
% 2.10/0.69    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | spl5_7),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f264,f276,f47])).
% 2.10/0.69  fof(f276,plain,(
% 2.10/0.69    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_7),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f117,f264,f49])).
% 2.10/0.69  fof(f117,plain,(
% 2.10/0.69    v1_xboole_0(sK1)),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f40,f93,f50])).
% 2.10/0.69  fof(f93,plain,(
% 2.10/0.69    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.10/0.69    inference(superposition,[],[f75,f78])).
% 2.10/0.69  fof(f264,plain,(
% 2.10/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl5_7),
% 2.10/0.69    inference(avatar_component_clause,[],[f262])).
% 2.10/0.69  fof(f563,plain,(
% 2.10/0.69    r2_hidden(sK3(sK1,sK1),sK1) | spl5_7),
% 2.10/0.69    inference(unit_resulting_resolution,[],[f516,f56])).
% 2.10/0.69  fof(f56,plain,(
% 2.10/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.10/0.69    inference(cnf_transformation,[],[f33])).
% 2.10/0.69  % SZS output end Proof for theBenchmark
% 2.10/0.69  % (2421)------------------------------
% 2.10/0.69  % (2421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.69  % (2421)Termination reason: Refutation
% 2.10/0.69  
% 2.10/0.69  % (2421)Memory used [KB]: 11257
% 2.10/0.69  % (2421)Time elapsed: 0.247 s
% 2.10/0.69  % (2421)------------------------------
% 2.10/0.69  % (2421)------------------------------
% 2.10/0.69  % (2393)Success in time 0.325 s
%------------------------------------------------------------------------------
