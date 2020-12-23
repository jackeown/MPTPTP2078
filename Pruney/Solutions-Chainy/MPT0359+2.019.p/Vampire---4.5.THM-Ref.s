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
% DateTime   : Thu Dec  3 12:44:41 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 211 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  271 ( 647 expanded)
%              Number of equality atoms :   74 ( 195 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f69,f109,f113,f313,f321,f413])).

fof(f413,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( sK0 != sK0
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f314,f393])).

fof(f393,plain,
    ( sK0 = sK1
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f383,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f383,plain,
    ( sK1 = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f163,f354])).

fof(f354,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f347,f335])).

fof(f335,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f327,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f327,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f141,f323])).

fof(f323,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f322,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f322,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f320,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
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

% (12075)Refutation not found, incomplete strategy% (12075)------------------------------
% (12075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f29,plain,(
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
    inference(rectify,[],[f28])).

% (12075)Termination reason: Refutation not found, incomplete strategy

% (12075)Memory used [KB]: 10618
% (12075)Time elapsed: 0.139 s
% (12075)------------------------------
% (12075)------------------------------
fof(f28,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f320,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f347,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f333,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f333,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f324,f332])).

fof(f332,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f315,f325])).

fof(f325,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f323,f40])).

fof(f315,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f32,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
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

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f324,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f62,f48])).

fof(f62,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f163,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f147,f73])).

fof(f73,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f41,f39])).

fof(f147,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f314,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(forward_demodulation,[],[f67,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f67,plain,
    ( sK1 != k2_subset_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_2
  <=> sK1 = k2_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f321,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f316,f318,f102])).

fof(f102,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f316,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f313,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f311,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f311,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f72,f310])).

fof(f310,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f309,f38])).

fof(f309,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f307,f118])).

fof(f118,plain,
    ( sK0 = k3_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f48,f114])).

fof(f114,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f108,f59])).

fof(f108,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_4
  <=> r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f307,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f71])).

fof(f71,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f32,f70])).

fof(f70,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f66,f37])).

fof(f66,plain,
    ( sK1 = k2_subset_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f63,f70])).

fof(f63,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f113,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f104,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f100,f65,f106,f102])).

fof(f100,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f71])).

fof(f69,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f33,f65,f61])).

fof(f33,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f65,f61])).

fof(f34,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (12090)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.47  % (12074)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (12069)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.52  % (12087)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.52  % (12077)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.52  % (12066)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.52  % (12079)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (12068)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.53  % (12073)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.53  % (12091)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.53  % (12087)Refutation not found, incomplete strategy% (12087)------------------------------
% 1.27/0.53  % (12087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (12087)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (12087)Memory used [KB]: 10746
% 1.27/0.53  % (12087)Time elapsed: 0.084 s
% 1.27/0.53  % (12087)------------------------------
% 1.27/0.53  % (12087)------------------------------
% 1.27/0.53  % (12071)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (12067)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (12065)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (12093)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (12072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (12084)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (12094)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (12085)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (12081)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (12080)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (12080)Refutation not found, incomplete strategy% (12080)------------------------------
% 1.35/0.54  % (12080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (12080)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (12080)Memory used [KB]: 6140
% 1.35/0.54  % (12080)Time elapsed: 0.003 s
% 1.35/0.54  % (12080)------------------------------
% 1.35/0.54  % (12080)------------------------------
% 1.35/0.54  % (12083)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (12086)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (12092)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (12089)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (12075)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (12077)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f414,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f68,f69,f109,f113,f313,f321,f413])).
% 1.35/0.55  fof(f413,plain,(
% 1.35/0.55    ~spl3_1 | spl3_2 | ~spl3_5),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f412])).
% 1.35/0.55  fof(f412,plain,(
% 1.35/0.55    $false | (~spl3_1 | spl3_2 | ~spl3_5)),
% 1.35/0.55    inference(trivial_inequality_removal,[],[f411])).
% 1.35/0.55  fof(f411,plain,(
% 1.35/0.55    sK0 != sK0 | (~spl3_1 | spl3_2 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f314,f393])).
% 1.35/0.55  fof(f393,plain,(
% 1.35/0.55    sK0 = sK1 | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(forward_demodulation,[],[f383,f39])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.35/0.55  fof(f383,plain,(
% 1.35/0.55    sK1 = k5_xboole_0(sK0,k1_xboole_0) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f163,f354])).
% 1.35/0.55  fof(f354,plain,(
% 1.35/0.55    k1_xboole_0 = k5_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(forward_demodulation,[],[f347,f335])).
% 1.35/0.55  fof(f335,plain,(
% 1.35/0.55    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.35/0.55    inference(forward_demodulation,[],[f327,f41])).
% 1.35/0.55  fof(f41,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.35/0.55  fof(f327,plain,(
% 1.35/0.55    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) | ~spl3_5),
% 1.35/0.55    inference(superposition,[],[f141,f323])).
% 1.35/0.55  fof(f323,plain,(
% 1.35/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 1.35/0.55    inference(resolution,[],[f322,f48])).
% 1.35/0.55  fof(f48,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.55  fof(f322,plain,(
% 1.35/0.55    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.35/0.55    inference(resolution,[],[f320,f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.35/0.55    inference(equality_resolution,[],[f52])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  % (12075)Refutation not found, incomplete strategy% (12075)------------------------------
% 1.35/0.55  % (12075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(rectify,[],[f28])).
% 1.35/0.55  % (12075)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (12075)Memory used [KB]: 10618
% 1.35/0.55  % (12075)Time elapsed: 0.139 s
% 1.35/0.55  % (12075)------------------------------
% 1.35/0.55  % (12075)------------------------------
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f11])).
% 1.35/0.55  fof(f11,axiom,(
% 1.35/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.35/0.55  fof(f320,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.35/0.55    inference(avatar_component_clause,[],[f318])).
% 1.35/0.55  fof(f318,plain,(
% 1.35/0.55    spl3_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.35/0.55  fof(f141,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(resolution,[],[f50,f42])).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.35/0.55  fof(f50,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(nnf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.35/0.55  fof(f347,plain,(
% 1.35/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f333,f40])).
% 1.35/0.55  fof(f40,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.55  fof(f333,plain,(
% 1.35/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(backward_demodulation,[],[f324,f332])).
% 1.35/0.55  fof(f332,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_5),
% 1.35/0.55    inference(backward_demodulation,[],[f315,f325])).
% 1.35/0.55  fof(f325,plain,(
% 1.35/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 1.35/0.55    inference(superposition,[],[f323,f40])).
% 1.35/0.55  fof(f315,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.35/0.55    inference(resolution,[],[f32,f57])).
% 1.35/0.55  fof(f57,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f49,f43])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f14])).
% 1.35/0.55  fof(f14,axiom,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(flattening,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,plain,(
% 1.35/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f17])).
% 1.35/0.55  fof(f17,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.35/0.55    inference(negated_conjecture,[],[f16])).
% 1.35/0.55  fof(f16,conjecture,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.35/0.55  fof(f324,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.35/0.55    inference(resolution,[],[f62,f48])).
% 1.35/0.55  fof(f62,plain,(
% 1.35/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f61])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.35/0.55  fof(f163,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.35/0.55    inference(forward_demodulation,[],[f147,f73])).
% 1.35/0.55  fof(f73,plain,(
% 1.35/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.35/0.55    inference(superposition,[],[f41,f39])).
% 1.35/0.55  fof(f147,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(superposition,[],[f56,f38])).
% 1.35/0.55  fof(f38,plain,(
% 1.35/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.35/0.55  fof(f56,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.35/0.55  fof(f314,plain,(
% 1.35/0.55    sK0 != sK1 | spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f67,f37])).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,axiom,(
% 1.35/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.55  fof(f67,plain,(
% 1.35/0.55    sK1 != k2_subset_1(sK0) | spl3_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f65])).
% 1.35/0.55  fof(f65,plain,(
% 1.35/0.55    spl3_2 <=> sK1 = k2_subset_1(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.35/0.55  fof(f321,plain,(
% 1.35/0.55    spl3_3 | spl3_5),
% 1.35/0.55    inference(avatar_split_clause,[],[f316,f318,f102])).
% 1.35/0.55  fof(f102,plain,(
% 1.35/0.55    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.35/0.55  fof(f316,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(resolution,[],[f32,f44])).
% 1.35/0.55  fof(f44,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f19])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,axiom,(
% 1.35/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.35/0.55  fof(f313,plain,(
% 1.35/0.55    spl3_1 | ~spl3_2 | ~spl3_4),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f312])).
% 1.35/0.55  fof(f312,plain,(
% 1.35/0.55    $false | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 1.35/0.55    inference(resolution,[],[f311,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.55  fof(f311,plain,(
% 1.35/0.55    ~r1_tarski(k1_xboole_0,sK0) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 1.35/0.55    inference(backward_demodulation,[],[f72,f310])).
% 1.35/0.55  fof(f310,plain,(
% 1.35/0.55    k1_xboole_0 = k3_subset_1(sK0,sK0) | (~spl3_2 | ~spl3_4)),
% 1.35/0.55    inference(forward_demodulation,[],[f309,f38])).
% 1.35/0.55  fof(f309,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) | (~spl3_2 | ~spl3_4)),
% 1.35/0.55    inference(forward_demodulation,[],[f307,f118])).
% 1.35/0.55  fof(f118,plain,(
% 1.35/0.55    sK0 = k3_xboole_0(sK0,sK0) | ~spl3_4),
% 1.35/0.55    inference(resolution,[],[f48,f114])).
% 1.35/0.55  fof(f114,plain,(
% 1.35/0.55    r1_tarski(sK0,sK0) | ~spl3_4),
% 1.35/0.55    inference(resolution,[],[f108,f59])).
% 1.35/0.55  fof(f108,plain,(
% 1.35/0.55    r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.35/0.55    inference(avatar_component_clause,[],[f106])).
% 1.35/0.55  fof(f106,plain,(
% 1.35/0.55    spl3_4 <=> r2_hidden(sK0,k1_zfmisc_1(sK0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.35/0.55  fof(f307,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl3_2),
% 1.35/0.55    inference(resolution,[],[f57,f71])).
% 1.35/0.55  fof(f71,plain,(
% 1.35/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.35/0.55    inference(backward_demodulation,[],[f32,f70])).
% 1.35/0.55  fof(f70,plain,(
% 1.35/0.55    sK0 = sK1 | ~spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f66,f37])).
% 1.35/0.55  fof(f66,plain,(
% 1.35/0.55    sK1 = k2_subset_1(sK0) | ~spl3_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f65])).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 1.35/0.55    inference(forward_demodulation,[],[f63,f70])).
% 1.35/0.55  fof(f63,plain,(
% 1.35/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f61])).
% 1.35/0.55  fof(f113,plain,(
% 1.35/0.55    ~spl3_3),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f110])).
% 1.35/0.55  fof(f110,plain,(
% 1.35/0.55    $false | ~spl3_3),
% 1.35/0.55    inference(resolution,[],[f104,f35])).
% 1.35/0.55  fof(f35,plain,(
% 1.35/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f15])).
% 1.35/0.55  fof(f15,axiom,(
% 1.35/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.35/0.55  fof(f104,plain,(
% 1.35/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.35/0.55    inference(avatar_component_clause,[],[f102])).
% 1.35/0.55  fof(f109,plain,(
% 1.35/0.55    spl3_3 | spl3_4 | ~spl3_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f100,f65,f106,f102])).
% 1.35/0.55  fof(f100,plain,(
% 1.35/0.55    r2_hidden(sK0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.35/0.55    inference(resolution,[],[f44,f71])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    spl3_1 | spl3_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f33,f65,f61])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f68,plain,(
% 1.35/0.55    ~spl3_1 | ~spl3_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f34,f65,f61])).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (12077)------------------------------
% 1.35/0.55  % (12077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (12077)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (12077)Memory used [KB]: 6396
% 1.35/0.55  % (12077)Time elapsed: 0.129 s
% 1.35/0.55  % (12077)------------------------------
% 1.35/0.55  % (12077)------------------------------
% 1.35/0.55  % (12078)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (12064)Success in time 0.193 s
%------------------------------------------------------------------------------
