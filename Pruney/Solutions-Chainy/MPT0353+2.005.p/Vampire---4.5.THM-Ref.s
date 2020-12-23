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
% DateTime   : Thu Dec  3 12:44:21 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 109 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 291 expanded)
%              Number of equality atoms :   49 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f110,f134,f168,f194,f528,f534])).

fof(f534,plain,
    ( ~ spl5_3
    | spl5_22 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | ~ spl5_3
    | spl5_22 ),
    inference(subsumption_resolution,[],[f531,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f531,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_22 ),
    inference(trivial_inequality_removal,[],[f530])).

fof(f530,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_22 ),
    inference(superposition,[],[f527,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f527,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl5_22
  <=> k7_subset_1(sK0,sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f528,plain,
    ( ~ spl5_22
    | ~ spl5_7
    | spl5_11 ),
    inference(avatar_split_clause,[],[f523,f191,f131,f525])).

fof(f131,plain,
    ( spl5_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f191,plain,
    ( spl5_11
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f523,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2)
    | ~ spl5_7
    | spl5_11 ),
    inference(subsumption_resolution,[],[f520,f133])).

fof(f133,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f520,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | spl5_11 ),
    inference(superposition,[],[f193,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f48,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f193,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f194,plain,
    ( ~ spl5_11
    | spl5_8 ),
    inference(avatar_split_clause,[],[f189,f165,f191])).

fof(f165,plain,
    ( spl5_8
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f189,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f179,f92])).

fof(f92,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f59,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f179,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | spl5_8 ),
    inference(superposition,[],[f167,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f167,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f168,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f163,f78,f73,f165])).

fof(f73,plain,
    ( spl5_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f78,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f163,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f162,f80])).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f162,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f75,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f134,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f128,f107,f131])).

fof(f107,plain,
    ( spl5_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f128,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f109,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f105,f83,f107])).

fof(f105,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f96,f64])).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f96,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f85])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f86,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f81,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (14161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (14150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (14161)Refutation not found, incomplete strategy% (14161)------------------------------
% 0.20/0.51  % (14161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14161)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14161)Memory used [KB]: 6140
% 0.20/0.51  % (14161)Time elapsed: 0.103 s
% 0.20/0.51  % (14161)------------------------------
% 0.20/0.51  % (14161)------------------------------
% 0.20/0.51  % (14153)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (14149)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (14148)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14151)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (14169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (14160)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (14166)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (14158)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14156)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (14146)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (14168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (14168)Refutation not found, incomplete strategy% (14168)------------------------------
% 0.20/0.53  % (14168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14168)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14168)Memory used [KB]: 10746
% 0.20/0.53  % (14168)Time elapsed: 0.091 s
% 0.20/0.53  % (14168)------------------------------
% 0.20/0.53  % (14168)------------------------------
% 0.20/0.54  % (14164)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (14172)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (14165)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (14152)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (14175)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (14174)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (14171)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (14163)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (14163)Refutation not found, incomplete strategy% (14163)------------------------------
% 0.20/0.54  % (14163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14163)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14163)Memory used [KB]: 10618
% 0.20/0.54  % (14163)Time elapsed: 0.137 s
% 0.20/0.54  % (14163)------------------------------
% 0.20/0.54  % (14163)------------------------------
% 0.20/0.54  % (14147)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (14167)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (14162)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (14157)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (14157)Refutation not found, incomplete strategy% (14157)------------------------------
% 0.20/0.55  % (14157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14157)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14157)Memory used [KB]: 10618
% 0.20/0.55  % (14157)Time elapsed: 0.144 s
% 0.20/0.55  % (14157)------------------------------
% 0.20/0.55  % (14157)------------------------------
% 0.20/0.55  % (14173)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (14154)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (14170)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (14155)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (14156)Refutation not found, incomplete strategy% (14156)------------------------------
% 0.20/0.55  % (14156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14156)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14156)Memory used [KB]: 10618
% 0.20/0.55  % (14156)Time elapsed: 0.146 s
% 0.20/0.55  % (14156)------------------------------
% 0.20/0.55  % (14156)------------------------------
% 0.20/0.56  % (14159)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.10/0.64  % (14176)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.68  % (14178)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.68  % (14179)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.70  % (14177)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.62/0.71  % (14178)Refutation found. Thanks to Tanya!
% 2.62/0.71  % SZS status Theorem for theBenchmark
% 2.62/0.71  % SZS output start Proof for theBenchmark
% 2.62/0.71  fof(f535,plain,(
% 2.62/0.71    $false),
% 2.62/0.71    inference(avatar_sat_refutation,[],[f76,f81,f86,f110,f134,f168,f194,f528,f534])).
% 2.62/0.71  fof(f534,plain,(
% 2.62/0.71    ~spl5_3 | spl5_22),
% 2.62/0.71    inference(avatar_contradiction_clause,[],[f533])).
% 2.62/0.71  fof(f533,plain,(
% 2.62/0.71    $false | (~spl5_3 | spl5_22)),
% 2.62/0.71    inference(subsumption_resolution,[],[f531,f85])).
% 2.62/0.73  fof(f85,plain,(
% 2.62/0.73    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_3),
% 2.62/0.73    inference(avatar_component_clause,[],[f83])).
% 2.62/0.73  fof(f83,plain,(
% 2.62/0.73    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.62/0.73  fof(f531,plain,(
% 2.62/0.73    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_22),
% 2.62/0.73    inference(trivial_inequality_removal,[],[f530])).
% 2.62/0.73  fof(f530,plain,(
% 2.62/0.73    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_22),
% 2.62/0.73    inference(superposition,[],[f527,f54])).
% 2.62/0.73  fof(f54,plain,(
% 2.62/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(cnf_transformation,[],[f22])).
% 2.62/0.73  fof(f22,plain,(
% 2.62/0.73    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.62/0.73    inference(ennf_transformation,[],[f15])).
% 2.62/0.73  fof(f15,axiom,(
% 2.62/0.73    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.62/0.73  fof(f527,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2) | spl5_22),
% 2.62/0.73    inference(avatar_component_clause,[],[f525])).
% 2.62/0.73  fof(f525,plain,(
% 2.62/0.73    spl5_22 <=> k7_subset_1(sK0,sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.62/0.73  fof(f528,plain,(
% 2.62/0.73    ~spl5_22 | ~spl5_7 | spl5_11),
% 2.62/0.73    inference(avatar_split_clause,[],[f523,f191,f131,f525])).
% 2.62/0.73  fof(f131,plain,(
% 2.62/0.73    spl5_7 <=> r1_tarski(sK1,sK0)),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.62/0.73  fof(f191,plain,(
% 2.62/0.73    spl5_11 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.62/0.73  fof(f523,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2) | (~spl5_7 | spl5_11)),
% 2.62/0.73    inference(subsumption_resolution,[],[f520,f133])).
% 2.62/0.73  fof(f133,plain,(
% 2.62/0.73    r1_tarski(sK1,sK0) | ~spl5_7),
% 2.62/0.73    inference(avatar_component_clause,[],[f131])).
% 2.62/0.73  fof(f520,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k4_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | spl5_11),
% 2.62/0.73    inference(superposition,[],[f193,f151])).
% 2.62/0.73  fof(f151,plain,(
% 2.62/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.62/0.73    inference(superposition,[],[f48,f65])).
% 2.62/0.73  fof(f65,plain,(
% 2.62/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.62/0.73    inference(cnf_transformation,[],[f24])).
% 2.62/0.73  fof(f24,plain,(
% 2.62/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.62/0.73    inference(ennf_transformation,[],[f4])).
% 2.62/0.73  fof(f4,axiom,(
% 2.62/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.62/0.73  fof(f48,plain,(
% 2.62/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.62/0.73    inference(cnf_transformation,[],[f6])).
% 2.62/0.73  fof(f6,axiom,(
% 2.62/0.73    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.62/0.73  fof(f193,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl5_11),
% 2.62/0.73    inference(avatar_component_clause,[],[f191])).
% 2.62/0.73  fof(f194,plain,(
% 2.62/0.73    ~spl5_11 | spl5_8),
% 2.62/0.73    inference(avatar_split_clause,[],[f189,f165,f191])).
% 2.62/0.73  fof(f165,plain,(
% 2.62/0.73    spl5_8 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.62/0.73  fof(f189,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl5_8),
% 2.62/0.73    inference(subsumption_resolution,[],[f179,f92])).
% 2.62/0.73  fof(f92,plain,(
% 2.62/0.73    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(backward_demodulation,[],[f59,f66])).
% 2.62/0.73  fof(f66,plain,(
% 2.62/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.62/0.73    inference(cnf_transformation,[],[f14])).
% 2.62/0.73  fof(f14,axiom,(
% 2.62/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.62/0.73  fof(f59,plain,(
% 2.62/0.73    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(cnf_transformation,[],[f12])).
% 2.62/0.73  fof(f12,axiom,(
% 2.62/0.73    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.62/0.73  fof(f179,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | spl5_8),
% 2.62/0.73    inference(superposition,[],[f167,f52])).
% 2.62/0.73  fof(f52,plain,(
% 2.62/0.73    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(cnf_transformation,[],[f20])).
% 2.62/0.73  fof(f20,plain,(
% 2.62/0.73    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.62/0.73    inference(ennf_transformation,[],[f16])).
% 2.62/0.73  fof(f16,axiom,(
% 2.62/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.62/0.73  fof(f167,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | spl5_8),
% 2.62/0.73    inference(avatar_component_clause,[],[f165])).
% 2.62/0.73  fof(f168,plain,(
% 2.62/0.73    ~spl5_8 | spl5_1 | ~spl5_2),
% 2.62/0.73    inference(avatar_split_clause,[],[f163,f78,f73,f165])).
% 2.62/0.73  fof(f73,plain,(
% 2.62/0.73    spl5_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.62/0.73  fof(f78,plain,(
% 2.62/0.73    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.62/0.73  fof(f163,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | (spl5_1 | ~spl5_2)),
% 2.62/0.73    inference(subsumption_resolution,[],[f162,f80])).
% 2.62/0.73  fof(f80,plain,(
% 2.62/0.73    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_2),
% 2.62/0.73    inference(avatar_component_clause,[],[f78])).
% 2.62/0.73  fof(f162,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_1),
% 2.62/0.73    inference(superposition,[],[f75,f53])).
% 2.62/0.73  fof(f53,plain,(
% 2.62/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(cnf_transformation,[],[f21])).
% 2.62/0.73  fof(f21,plain,(
% 2.62/0.73    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.62/0.73    inference(ennf_transformation,[],[f11])).
% 2.62/0.73  fof(f11,axiom,(
% 2.62/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.62/0.73  fof(f75,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl5_1),
% 2.62/0.73    inference(avatar_component_clause,[],[f73])).
% 2.62/0.73  fof(f134,plain,(
% 2.62/0.73    spl5_7 | ~spl5_5),
% 2.62/0.73    inference(avatar_split_clause,[],[f128,f107,f131])).
% 2.62/0.73  fof(f107,plain,(
% 2.62/0.73    spl5_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.62/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.62/0.73  fof(f128,plain,(
% 2.62/0.73    r1_tarski(sK1,sK0) | ~spl5_5),
% 2.62/0.73    inference(resolution,[],[f109,f71])).
% 2.62/0.73  fof(f71,plain,(
% 2.62/0.73    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.62/0.73    inference(equality_resolution,[],[f60])).
% 2.62/0.73  fof(f60,plain,(
% 2.62/0.73    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.62/0.73    inference(cnf_transformation,[],[f37])).
% 2.62/0.73  fof(f37,plain,(
% 2.62/0.73    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.62/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.62/0.73  fof(f36,plain,(
% 2.62/0.73    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.62/0.73    introduced(choice_axiom,[])).
% 2.62/0.73  fof(f35,plain,(
% 2.62/0.73    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.62/0.73    inference(rectify,[],[f34])).
% 2.62/0.73  fof(f34,plain,(
% 2.62/0.73    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.62/0.73    inference(nnf_transformation,[],[f8])).
% 2.62/0.73  fof(f8,axiom,(
% 2.62/0.73    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.62/0.73  fof(f109,plain,(
% 2.62/0.73    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_5),
% 2.62/0.73    inference(avatar_component_clause,[],[f107])).
% 2.62/0.73  fof(f110,plain,(
% 2.62/0.73    spl5_5 | ~spl5_3),
% 2.62/0.73    inference(avatar_split_clause,[],[f105,f83,f107])).
% 2.62/0.73  fof(f105,plain,(
% 2.62/0.73    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_3),
% 2.62/0.73    inference(subsumption_resolution,[],[f96,f64])).
% 2.62/0.73  fof(f64,plain,(
% 2.62/0.73    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.62/0.73    inference(cnf_transformation,[],[f13])).
% 2.62/0.73  fof(f13,axiom,(
% 2.62/0.73    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.62/0.73  fof(f96,plain,(
% 2.62/0.73    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_3),
% 2.62/0.73    inference(resolution,[],[f55,f85])).
% 2.62/0.73  fof(f55,plain,(
% 2.62/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.62/0.73    inference(cnf_transformation,[],[f33])).
% 2.62/0.73  fof(f33,plain,(
% 2.62/0.73    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.62/0.73    inference(nnf_transformation,[],[f23])).
% 2.62/0.73  fof(f23,plain,(
% 2.62/0.73    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.62/0.73    inference(ennf_transformation,[],[f10])).
% 2.62/0.73  fof(f10,axiom,(
% 2.62/0.73    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.62/0.73  fof(f86,plain,(
% 2.62/0.73    spl5_3),
% 2.62/0.73    inference(avatar_split_clause,[],[f38,f83])).
% 2.62/0.73  fof(f38,plain,(
% 2.62/0.73    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.62/0.73    inference(cnf_transformation,[],[f27])).
% 2.62/0.73  fof(f27,plain,(
% 2.62/0.73    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.62/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26,f25])).
% 2.62/0.73  fof(f25,plain,(
% 2.62/0.73    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.62/0.73    introduced(choice_axiom,[])).
% 2.62/0.73  fof(f26,plain,(
% 2.62/0.73    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.62/0.73    introduced(choice_axiom,[])).
% 2.62/0.73  fof(f19,plain,(
% 2.62/0.73    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.62/0.73    inference(ennf_transformation,[],[f18])).
% 2.62/0.73  fof(f18,negated_conjecture,(
% 2.62/0.73    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.62/0.73    inference(negated_conjecture,[],[f17])).
% 2.62/0.73  fof(f17,conjecture,(
% 2.62/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.62/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.62/0.73  fof(f81,plain,(
% 2.62/0.73    spl5_2),
% 2.62/0.73    inference(avatar_split_clause,[],[f39,f78])).
% 2.62/0.73  fof(f39,plain,(
% 2.62/0.73    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.62/0.73    inference(cnf_transformation,[],[f27])).
% 2.62/0.73  fof(f76,plain,(
% 2.62/0.73    ~spl5_1),
% 2.62/0.73    inference(avatar_split_clause,[],[f40,f73])).
% 2.62/0.73  fof(f40,plain,(
% 2.62/0.73    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.62/0.73    inference(cnf_transformation,[],[f27])).
% 2.62/0.73  % SZS output end Proof for theBenchmark
% 2.62/0.73  % (14178)------------------------------
% 2.62/0.73  % (14178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.62/0.73  % (14178)Termination reason: Refutation
% 2.62/0.73  
% 2.62/0.73  % (14178)Memory used [KB]: 6652
% 2.62/0.73  % (14178)Time elapsed: 0.130 s
% 2.62/0.73  % (14178)------------------------------
% 2.62/0.73  % (14178)------------------------------
% 2.62/0.73  % (14145)Success in time 0.375 s
%------------------------------------------------------------------------------
