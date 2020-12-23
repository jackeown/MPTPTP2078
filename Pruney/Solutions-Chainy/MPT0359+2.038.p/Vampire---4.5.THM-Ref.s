%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:43 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 170 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 ( 501 expanded)
%              Number of equality atoms :   65 ( 165 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f130,f143,f236,f239])).

fof(f239,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f141,f148])).

fof(f148,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f147,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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

fof(f147,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f145,f40])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f145,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f141,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f236,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f234,f137])).

fof(f137,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f234,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f59,f218])).

fof(f218,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f165,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f178,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f178,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f78,f144])).

fof(f144,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f78,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f165,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f143,plain,
    ( ~ spl3_4
    | ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f133,f81,f135,f139])).

fof(f81,plain,
    ( spl3_2
  <=> sK1 = k2_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK1,sK0)
    | spl3_2 ),
    inference(extensionality_resolution,[],[f54,f131])).

fof(f131,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(forward_demodulation,[],[f83,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f83,plain,
    ( sK1 != k2_subset_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f128,f116])).

fof(f116,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f109,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f65,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f60,f72])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f87,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f124,f103])).

fof(f124,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f51,f88])).

fof(f88,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f37,f86])).

fof(f86,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f82,f41])).

fof(f82,plain,
    ( sK1 = k2_subset_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f79,f86])).

fof(f79,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f85,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f38,f81,f77])).

fof(f38,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f81,f77])).

fof(f39,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.56  % (26668)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.57  % (26660)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.58/0.58  % (26654)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.58/0.58  % (26667)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.58/0.58  % (26651)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.73/0.59  % (26652)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.73/0.59  % (26676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.73/0.59  % (26656)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.73/0.59  % (26659)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.73/0.59  % (26655)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.73/0.59  % (26653)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.59  % (26652)Refutation not found, incomplete strategy% (26652)------------------------------
% 1.73/0.59  % (26652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (26652)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (26652)Memory used [KB]: 1663
% 1.73/0.59  % (26652)Time elapsed: 0.165 s
% 1.73/0.59  % (26652)------------------------------
% 1.73/0.59  % (26652)------------------------------
% 1.73/0.60  % (26667)Refutation not found, incomplete strategy% (26667)------------------------------
% 1.73/0.60  % (26667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (26667)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (26667)Memory used [KB]: 10618
% 1.73/0.60  % (26667)Time elapsed: 0.156 s
% 1.73/0.60  % (26667)------------------------------
% 1.73/0.60  % (26667)------------------------------
% 1.73/0.60  % (26679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.60  % (26674)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.73/0.60  % (26673)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.60  % (26679)Refutation not found, incomplete strategy% (26679)------------------------------
% 1.73/0.60  % (26679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (26679)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (26679)Memory used [KB]: 10746
% 1.73/0.60  % (26679)Time elapsed: 0.172 s
% 1.73/0.60  % (26679)------------------------------
% 1.73/0.60  % (26679)------------------------------
% 1.73/0.60  % (26666)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.60  % (26678)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.73/0.60  % (26678)Refutation not found, incomplete strategy% (26678)------------------------------
% 1.73/0.60  % (26678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (26678)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (26678)Memory used [KB]: 6268
% 1.73/0.60  % (26678)Time elapsed: 0.172 s
% 1.73/0.60  % (26678)------------------------------
% 1.73/0.60  % (26678)------------------------------
% 1.73/0.60  % (26657)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.73/0.60  % (26661)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.73/0.60  % (26664)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.73/0.61  % (26669)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.73/0.61  % (26661)Refutation not found, incomplete strategy% (26661)------------------------------
% 1.73/0.61  % (26661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (26661)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (26661)Memory used [KB]: 10746
% 1.73/0.61  % (26661)Time elapsed: 0.172 s
% 1.73/0.61  % (26661)------------------------------
% 1.73/0.61  % (26661)------------------------------
% 1.73/0.61  % (26669)Refutation not found, incomplete strategy% (26669)------------------------------
% 1.73/0.61  % (26669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (26669)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (26669)Memory used [KB]: 1663
% 1.73/0.61  % (26669)Time elapsed: 0.172 s
% 1.73/0.61  % (26669)------------------------------
% 1.73/0.61  % (26669)------------------------------
% 1.73/0.61  % (26657)Refutation found. Thanks to Tanya!
% 1.73/0.61  % SZS status Theorem for theBenchmark
% 1.73/0.61  % SZS output start Proof for theBenchmark
% 1.73/0.61  fof(f240,plain,(
% 1.73/0.61    $false),
% 1.73/0.61    inference(avatar_sat_refutation,[],[f84,f85,f130,f143,f236,f239])).
% 1.73/0.61  fof(f239,plain,(
% 1.73/0.61    spl3_4),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f238])).
% 1.73/0.61  fof(f238,plain,(
% 1.73/0.61    $false | spl3_4),
% 1.73/0.61    inference(subsumption_resolution,[],[f141,f148])).
% 1.73/0.61  fof(f148,plain,(
% 1.73/0.61    r1_tarski(sK1,sK0)),
% 1.73/0.61    inference(resolution,[],[f147,f75])).
% 1.73/0.61  fof(f75,plain,(
% 1.73/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f55])).
% 1.73/0.61  fof(f55,plain,(
% 1.73/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f35])).
% 1.73/0.61  fof(f35,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.73/0.61  fof(f34,plain,(
% 1.73/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f33,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.73/0.61    inference(rectify,[],[f32])).
% 1.73/0.61  fof(f32,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.73/0.61    inference(nnf_transformation,[],[f12])).
% 1.73/0.61  fof(f12,axiom,(
% 1.73/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.73/0.61  fof(f147,plain,(
% 1.73/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.73/0.61    inference(subsumption_resolution,[],[f145,f40])).
% 1.73/0.61  fof(f40,plain,(
% 1.73/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,axiom,(
% 1.73/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.73/0.61  fof(f145,plain,(
% 1.73/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.73/0.61    inference(resolution,[],[f37,f47])).
% 1.73/0.61  fof(f47,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f29])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.73/0.61    inference(nnf_transformation,[],[f22])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.73/0.61    inference(ennf_transformation,[],[f14])).
% 1.73/0.61  fof(f14,axiom,(
% 1.73/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.73/0.61    inference(cnf_transformation,[],[f28])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 1.73/0.61  fof(f27,plain,(
% 1.73/0.61    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f26,plain,(
% 1.73/0.61    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.61    inference(flattening,[],[f25])).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.61    inference(nnf_transformation,[],[f21])).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.61    inference(ennf_transformation,[],[f19])).
% 1.73/0.61  fof(f19,negated_conjecture,(
% 1.73/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.73/0.61    inference(negated_conjecture,[],[f18])).
% 1.73/0.61  fof(f18,conjecture,(
% 1.73/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.73/0.61  fof(f141,plain,(
% 1.73/0.61    ~r1_tarski(sK1,sK0) | spl3_4),
% 1.73/0.61    inference(avatar_component_clause,[],[f139])).
% 1.73/0.61  fof(f139,plain,(
% 1.73/0.61    spl3_4 <=> r1_tarski(sK1,sK0)),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.73/0.61  fof(f236,plain,(
% 1.73/0.61    ~spl3_1 | spl3_3),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f235])).
% 1.73/0.61  fof(f235,plain,(
% 1.73/0.61    $false | (~spl3_1 | spl3_3)),
% 1.73/0.61    inference(subsumption_resolution,[],[f234,f137])).
% 1.73/0.61  fof(f137,plain,(
% 1.73/0.61    ~r1_tarski(sK0,sK1) | spl3_3),
% 1.73/0.61    inference(avatar_component_clause,[],[f135])).
% 1.73/0.61  fof(f135,plain,(
% 1.73/0.61    spl3_3 <=> r1_tarski(sK0,sK1)),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.73/0.61  fof(f234,plain,(
% 1.73/0.61    r1_tarski(sK0,sK1) | ~spl3_1),
% 1.73/0.61    inference(trivial_inequality_removal,[],[f233])).
% 1.73/0.61  fof(f233,plain,(
% 1.73/0.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl3_1),
% 1.73/0.61    inference(superposition,[],[f59,f218])).
% 1.73/0.61  fof(f218,plain,(
% 1.73/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 1.73/0.61    inference(superposition,[],[f165,f181])).
% 1.73/0.61  fof(f181,plain,(
% 1.73/0.61    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl3_1),
% 1.73/0.61    inference(resolution,[],[f178,f60])).
% 1.73/0.61  fof(f60,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f36])).
% 1.73/0.61  fof(f36,plain,(
% 1.73/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.73/0.61    inference(nnf_transformation,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.73/0.61  fof(f178,plain,(
% 1.73/0.61    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl3_1),
% 1.73/0.61    inference(backward_demodulation,[],[f78,f144])).
% 1.73/0.61  fof(f144,plain,(
% 1.73/0.61    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.73/0.61    inference(resolution,[],[f37,f51])).
% 1.73/0.61  fof(f51,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f23])).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.61    inference(ennf_transformation,[],[f16])).
% 1.73/0.61  fof(f16,axiom,(
% 1.73/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.73/0.61  fof(f78,plain,(
% 1.73/0.61    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.73/0.61    inference(avatar_component_clause,[],[f77])).
% 1.73/0.61  fof(f77,plain,(
% 1.73/0.61    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.73/0.61  fof(f165,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.73/0.61    inference(superposition,[],[f68,f67])).
% 1.73/0.61  fof(f67,plain,(
% 1.73/0.61    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.73/0.61    inference(definition_unfolding,[],[f43,f66])).
% 1.73/0.61  fof(f66,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.73/0.61    inference(definition_unfolding,[],[f44,f45])).
% 1.73/0.61  fof(f45,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f11])).
% 1.73/0.61  fof(f11,axiom,(
% 1.73/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.61  fof(f44,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f13])).
% 1.73/0.61  fof(f13,axiom,(
% 1.73/0.61    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.73/0.61  fof(f43,plain,(
% 1.73/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f20])).
% 1.73/0.61  fof(f20,plain,(
% 1.73/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.73/0.61    inference(rectify,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.73/0.61  fof(f68,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.73/0.61    inference(definition_unfolding,[],[f61,f66])).
% 1.73/0.61  fof(f61,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f8])).
% 1.73/0.61  fof(f8,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.73/0.61  fof(f59,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f36])).
% 1.73/0.61  fof(f143,plain,(
% 1.73/0.61    ~spl3_4 | ~spl3_3 | spl3_2),
% 1.73/0.61    inference(avatar_split_clause,[],[f133,f81,f135,f139])).
% 1.73/0.61  fof(f81,plain,(
% 1.73/0.61    spl3_2 <=> sK1 = k2_subset_1(sK0)),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.73/0.61  fof(f133,plain,(
% 1.73/0.61    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK1,sK0) | spl3_2),
% 1.73/0.61    inference(extensionality_resolution,[],[f54,f131])).
% 1.73/0.61  fof(f131,plain,(
% 1.73/0.61    sK0 != sK1 | spl3_2),
% 1.73/0.61    inference(forward_demodulation,[],[f83,f41])).
% 1.73/0.61  fof(f41,plain,(
% 1.73/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f15])).
% 1.73/0.61  fof(f15,axiom,(
% 1.73/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.73/0.61  fof(f83,plain,(
% 1.73/0.61    sK1 != k2_subset_1(sK0) | spl3_2),
% 1.73/0.61    inference(avatar_component_clause,[],[f81])).
% 1.73/0.61  fof(f54,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  fof(f31,plain,(
% 1.73/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/0.61    inference(flattening,[],[f30])).
% 1.73/0.61  fof(f30,plain,(
% 1.73/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/0.61    inference(nnf_transformation,[],[f2])).
% 1.73/0.61  fof(f2,axiom,(
% 1.73/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.73/0.61  fof(f130,plain,(
% 1.73/0.61    spl3_1 | ~spl3_2),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f129])).
% 1.73/0.61  fof(f129,plain,(
% 1.73/0.61    $false | (spl3_1 | ~spl3_2)),
% 1.73/0.61    inference(subsumption_resolution,[],[f128,f116])).
% 1.73/0.61  fof(f116,plain,(
% 1.73/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.73/0.61    inference(resolution,[],[f109,f72])).
% 1.73/0.61  fof(f72,plain,(
% 1.73/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.73/0.61    inference(equality_resolution,[],[f53])).
% 1.73/0.61  fof(f53,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  fof(f109,plain,(
% 1.73/0.61    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X3)) )),
% 1.73/0.61    inference(superposition,[],[f65,f103])).
% 1.73/0.61  fof(f103,plain,(
% 1.73/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.73/0.61    inference(resolution,[],[f60,f72])).
% 1.73/0.61  fof(f65,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f24])).
% 1.73/0.61  fof(f24,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f5])).
% 1.73/0.61  fof(f5,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.73/0.61  fof(f128,plain,(
% 1.73/0.61    ~r1_tarski(k1_xboole_0,sK0) | (spl3_1 | ~spl3_2)),
% 1.73/0.61    inference(backward_demodulation,[],[f87,f127])).
% 1.73/0.61  fof(f127,plain,(
% 1.73/0.61    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl3_2),
% 1.73/0.61    inference(forward_demodulation,[],[f124,f103])).
% 1.73/0.61  fof(f124,plain,(
% 1.73/0.61    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl3_2),
% 1.73/0.61    inference(resolution,[],[f51,f88])).
% 1.73/0.61  fof(f88,plain,(
% 1.73/0.61    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.73/0.61    inference(backward_demodulation,[],[f37,f86])).
% 1.73/0.61  fof(f86,plain,(
% 1.73/0.61    sK0 = sK1 | ~spl3_2),
% 1.73/0.61    inference(backward_demodulation,[],[f82,f41])).
% 1.73/0.61  fof(f82,plain,(
% 1.73/0.61    sK1 = k2_subset_1(sK0) | ~spl3_2),
% 1.73/0.61    inference(avatar_component_clause,[],[f81])).
% 1.73/0.61  fof(f87,plain,(
% 1.73/0.61    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 1.73/0.61    inference(backward_demodulation,[],[f79,f86])).
% 1.73/0.61  fof(f79,plain,(
% 1.73/0.61    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 1.73/0.61    inference(avatar_component_clause,[],[f77])).
% 1.73/0.61  fof(f85,plain,(
% 1.73/0.61    spl3_1 | spl3_2),
% 1.73/0.61    inference(avatar_split_clause,[],[f38,f81,f77])).
% 1.73/0.61  fof(f38,plain,(
% 1.73/0.61    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.73/0.61    inference(cnf_transformation,[],[f28])).
% 1.73/0.61  fof(f84,plain,(
% 1.73/0.61    ~spl3_1 | ~spl3_2),
% 1.73/0.61    inference(avatar_split_clause,[],[f39,f81,f77])).
% 1.73/0.61  fof(f39,plain,(
% 1.73/0.61    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.73/0.61    inference(cnf_transformation,[],[f28])).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (26657)------------------------------
% 1.73/0.61  % (26657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (26657)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (26657)Memory used [KB]: 10746
% 1.73/0.61  % (26657)Time elapsed: 0.167 s
% 1.73/0.61  % (26657)------------------------------
% 1.73/0.61  % (26657)------------------------------
% 1.73/0.61  % (26650)Success in time 0.243 s
%------------------------------------------------------------------------------
