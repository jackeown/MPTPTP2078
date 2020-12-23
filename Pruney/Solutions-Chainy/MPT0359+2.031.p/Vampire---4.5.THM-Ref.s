%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:42 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 228 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 ( 704 expanded)
%              Number of equality atoms :   61 ( 219 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f83,f91,f98,f184])).

fof(f184,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f64,f165])).

fof(f165,plain,
    ( sK0 = sK1
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f118,f150])).

fof(f150,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f148,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f143,f144])).

fof(f144,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f111,f124])).

fof(f124,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f92,f118])).

fof(f92,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f30,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
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

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f111,plain,
    ( sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f110,f92])).

fof(f110,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f101,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f97,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f143,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f53,f127])).

fof(f127,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f103,f124])).

fof(f103,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f99,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f99,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f118,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f109,f38])).

fof(f109,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f46])).

fof(f64,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f93,f96,f75])).

fof(f75,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f93,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f91,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f81,f87])).

fof(f87,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f53,f71])).

fof(f71,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_subset_1(sK0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f55])).

fof(f70,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f30,f68])).

fof(f68,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f61,f68])).

fof(f61,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f83,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f76,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f69,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f66,f63,f60])).

fof(f66,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f31,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f63,f60])).

fof(f58,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f32,f35])).

fof(f32,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (812613632)
% 1.00/0.65  % (24231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.14/0.67  % (24240)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.14/0.67  % (24256)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.14/0.67  % (24231)Refutation found. Thanks to Tanya!
% 1.14/0.67  % SZS status Theorem for theBenchmark
% 1.14/0.68  % (24233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.14/0.68  % (24248)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.14/0.68  % (24230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.14/0.68  % (24239)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.14/0.68  % (24239)Refutation not found, incomplete strategy% (24239)------------------------------
% 1.14/0.68  % (24239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.68  % (24239)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.68  
% 1.14/0.68  % (24239)Memory used [KB]: 10618
% 1.14/0.68  % (24239)Time elapsed: 0.116 s
% 1.14/0.68  % (24239)------------------------------
% 1.14/0.68  % (24239)------------------------------
% 1.14/0.68  % SZS output start Proof for theBenchmark
% 1.14/0.68  fof(f193,plain,(
% 1.14/0.68    $false),
% 1.14/0.68    inference(avatar_sat_refutation,[],[f65,f69,f83,f91,f98,f184])).
% 1.14/0.68  fof(f184,plain,(
% 1.14/0.68    ~spl3_1 | spl3_2 | ~spl3_5),
% 1.14/0.68    inference(avatar_contradiction_clause,[],[f169])).
% 1.14/0.68  fof(f169,plain,(
% 1.14/0.68    $false | (~spl3_1 | spl3_2 | ~spl3_5)),
% 1.14/0.68    inference(subsumption_resolution,[],[f64,f165])).
% 1.14/0.68  fof(f165,plain,(
% 1.14/0.68    sK0 = sK1 | (~spl3_1 | ~spl3_5)),
% 1.14/0.68    inference(backward_demodulation,[],[f118,f150])).
% 1.14/0.68  fof(f150,plain,(
% 1.14/0.68    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 1.14/0.68    inference(resolution,[],[f148,f46])).
% 1.14/0.68  fof(f46,plain,(
% 1.14/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.14/0.68    inference(cnf_transformation,[],[f19])).
% 1.14/0.68  fof(f19,plain,(
% 1.14/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.14/0.68    inference(ennf_transformation,[],[f4])).
% 1.14/0.68  fof(f4,axiom,(
% 1.14/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.14/0.68  fof(f148,plain,(
% 1.14/0.68    r1_tarski(sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 1.14/0.68    inference(backward_demodulation,[],[f143,f144])).
% 1.14/0.68  fof(f144,plain,(
% 1.14/0.68    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.14/0.68    inference(forward_demodulation,[],[f111,f124])).
% 1.14/0.68  fof(f124,plain,(
% 1.14/0.68    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_5),
% 1.14/0.68    inference(backward_demodulation,[],[f92,f118])).
% 1.14/0.68  fof(f92,plain,(
% 1.14/0.68    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.14/0.68    inference(resolution,[],[f30,f55])).
% 1.14/0.68  fof(f55,plain,(
% 1.14/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.14/0.68    inference(definition_unfolding,[],[f47,f40])).
% 1.14/0.68  fof(f40,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.14/0.68    inference(cnf_transformation,[],[f2])).
% 1.14/0.68  fof(f2,axiom,(
% 1.14/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.14/0.68  fof(f47,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.14/0.68    inference(cnf_transformation,[],[f20])).
% 1.14/0.68  fof(f20,plain,(
% 1.14/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.14/0.68    inference(ennf_transformation,[],[f12])).
% 1.14/0.68  fof(f12,axiom,(
% 1.14/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.14/0.68  fof(f30,plain,(
% 1.14/0.68    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.14/0.68    inference(cnf_transformation,[],[f24])).
% 1.14/0.68  fof(f24,plain,(
% 1.14/0.68    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.14/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.14/0.68  fof(f23,plain,(
% 1.14/0.68    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.14/0.68    introduced(choice_axiom,[])).
% 1.14/0.68  fof(f22,plain,(
% 1.14/0.68    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.14/0.68    inference(flattening,[],[f21])).
% 1.14/0.68  fof(f21,plain,(
% 1.14/0.68    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.14/0.68    inference(nnf_transformation,[],[f16])).
% 1.14/0.68  fof(f16,plain,(
% 1.14/0.68    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.14/0.68    inference(ennf_transformation,[],[f15])).
% 1.14/0.68  fof(f15,negated_conjecture,(
% 1.14/0.68    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.14/0.68    inference(negated_conjecture,[],[f14])).
% 1.14/0.68  fof(f14,conjecture,(
% 1.14/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.14/0.68  fof(f111,plain,(
% 1.14/0.68    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl3_5),
% 1.14/0.68    inference(forward_demodulation,[],[f110,f92])).
% 1.14/0.68  fof(f110,plain,(
% 1.14/0.68    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.14/0.68    inference(resolution,[],[f101,f54])).
% 1.14/0.68  fof(f54,plain,(
% 1.14/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.14/0.68    inference(definition_unfolding,[],[f45,f52])).
% 1.14/0.68  fof(f52,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.14/0.68    inference(definition_unfolding,[],[f39,f40])).
% 1.14/0.68  fof(f39,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.14/0.68    inference(cnf_transformation,[],[f8])).
% 1.14/0.68  fof(f8,axiom,(
% 1.14/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.14/0.68  fof(f45,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.14/0.68    inference(cnf_transformation,[],[f18])).
% 1.14/0.68  fof(f18,plain,(
% 1.14/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.14/0.68    inference(ennf_transformation,[],[f3])).
% 1.14/0.68  fof(f3,axiom,(
% 1.14/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.14/0.68  fof(f101,plain,(
% 1.14/0.68    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.14/0.68    inference(resolution,[],[f97,f57])).
% 1.14/0.68  fof(f57,plain,(
% 1.14/0.68    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.14/0.68    inference(equality_resolution,[],[f48])).
% 1.14/0.68  fof(f48,plain,(
% 1.14/0.68    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.14/0.68    inference(cnf_transformation,[],[f29])).
% 1.14/0.68  fof(f29,plain,(
% 1.14/0.68    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.14/0.68  fof(f28,plain,(
% 1.14/0.68    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.14/0.68    introduced(choice_axiom,[])).
% 1.14/0.68  fof(f27,plain,(
% 1.14/0.68    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.68    inference(rectify,[],[f26])).
% 1.14/0.68  fof(f26,plain,(
% 1.14/0.68    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.68    inference(nnf_transformation,[],[f9])).
% 1.14/0.68  fof(f9,axiom,(
% 1.14/0.68    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.14/0.68  fof(f97,plain,(
% 1.14/0.68    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.14/0.68    inference(avatar_component_clause,[],[f96])).
% 1.14/0.68  fof(f96,plain,(
% 1.14/0.68    spl3_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.14/0.68  fof(f143,plain,(
% 1.14/0.68    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | (~spl3_1 | ~spl3_5)),
% 1.14/0.68    inference(superposition,[],[f53,f127])).
% 1.14/0.68  fof(f127,plain,(
% 1.14/0.68    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_5)),
% 1.14/0.68    inference(backward_demodulation,[],[f103,f124])).
% 1.14/0.68  fof(f103,plain,(
% 1.14/0.68    k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl3_1),
% 1.14/0.68    inference(superposition,[],[f99,f38])).
% 1.14/0.68  fof(f38,plain,(
% 1.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.14/0.68    inference(cnf_transformation,[],[f1])).
% 1.14/0.68  fof(f1,axiom,(
% 1.14/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.14/0.68  fof(f99,plain,(
% 1.14/0.68    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.14/0.68    inference(resolution,[],[f67,f46])).
% 1.14/0.68  fof(f67,plain,(
% 1.14/0.68    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.14/0.68    inference(avatar_component_clause,[],[f60])).
% 1.14/0.68  fof(f60,plain,(
% 1.14/0.68    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.14/0.68  fof(f53,plain,(
% 1.14/0.68    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.14/0.68    inference(definition_unfolding,[],[f37,f40])).
% 1.14/0.68  fof(f37,plain,(
% 1.14/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.14/0.68    inference(cnf_transformation,[],[f6])).
% 1.14/0.68  fof(f6,axiom,(
% 1.14/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.14/0.68  fof(f118,plain,(
% 1.14/0.68    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 1.14/0.68    inference(superposition,[],[f109,f38])).
% 1.14/0.68  fof(f109,plain,(
% 1.14/0.68    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 1.14/0.68    inference(resolution,[],[f101,f46])).
% 1.14/0.68  fof(f64,plain,(
% 1.14/0.68    sK0 != sK1 | spl3_2),
% 1.14/0.68    inference(avatar_component_clause,[],[f63])).
% 1.14/0.68  fof(f63,plain,(
% 1.14/0.68    spl3_2 <=> sK0 = sK1),
% 1.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.14/0.68  fof(f98,plain,(
% 1.14/0.68    spl3_3 | spl3_5),
% 1.14/0.68    inference(avatar_split_clause,[],[f93,f96,f75])).
% 1.14/0.68  fof(f75,plain,(
% 1.14/0.68    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.14/0.68  fof(f93,plain,(
% 1.14/0.68    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.14/0.68    inference(resolution,[],[f30,f41])).
% 1.14/0.68  fof(f41,plain,(
% 1.14/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.14/0.68    inference(cnf_transformation,[],[f25])).
% 1.14/0.68  fof(f25,plain,(
% 1.14/0.68    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.14/0.68    inference(nnf_transformation,[],[f17])).
% 1.14/0.68  fof(f17,plain,(
% 1.14/0.68    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.14/0.68    inference(ennf_transformation,[],[f10])).
% 1.14/0.68  fof(f10,axiom,(
% 1.14/0.68    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.14/0.68  fof(f91,plain,(
% 1.14/0.68    spl3_1 | ~spl3_2),
% 1.14/0.68    inference(avatar_contradiction_clause,[],[f88])).
% 1.14/0.68  fof(f88,plain,(
% 1.14/0.68    $false | (spl3_1 | ~spl3_2)),
% 1.14/0.68    inference(subsumption_resolution,[],[f81,f87])).
% 1.14/0.68  fof(f87,plain,(
% 1.14/0.68    r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl3_2),
% 1.14/0.68    inference(superposition,[],[f53,f71])).
% 1.14/0.68  fof(f71,plain,(
% 1.14/0.68    k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_subset_1(sK0,sK0) | ~spl3_2),
% 1.14/0.68    inference(resolution,[],[f70,f55])).
% 1.14/0.68  fof(f70,plain,(
% 1.14/0.68    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.14/0.68    inference(forward_demodulation,[],[f30,f68])).
% 1.14/0.68  fof(f68,plain,(
% 1.14/0.68    sK0 = sK1 | ~spl3_2),
% 1.14/0.68    inference(avatar_component_clause,[],[f63])).
% 1.14/0.68  fof(f81,plain,(
% 1.14/0.68    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 1.14/0.68    inference(forward_demodulation,[],[f61,f68])).
% 1.14/0.69  fof(f61,plain,(
% 1.14/0.69    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 1.14/0.69    inference(avatar_component_clause,[],[f60])).
% 1.14/0.69  fof(f83,plain,(
% 1.14/0.69    ~spl3_3),
% 1.14/0.69    inference(avatar_contradiction_clause,[],[f82])).
% 1.14/0.69  fof(f82,plain,(
% 1.14/0.69    $false | ~spl3_3),
% 1.14/0.69    inference(resolution,[],[f76,f33])).
% 1.14/0.69  fof(f33,plain,(
% 1.14/0.69    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.14/0.69    inference(cnf_transformation,[],[f13])).
% 1.14/0.69  fof(f13,axiom,(
% 1.14/0.69    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.14/0.69  fof(f76,plain,(
% 1.14/0.69    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.14/0.69    inference(avatar_component_clause,[],[f75])).
% 1.14/0.69  fof(f69,plain,(
% 1.14/0.69    spl3_1 | spl3_2),
% 1.14/0.69    inference(avatar_split_clause,[],[f66,f63,f60])).
% 1.14/0.69  fof(f66,plain,(
% 1.14/0.69    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.14/0.69    inference(forward_demodulation,[],[f31,f35])).
% 1.14/0.69  fof(f35,plain,(
% 1.14/0.69    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.14/0.69    inference(cnf_transformation,[],[f11])).
% 1.14/0.69  fof(f11,axiom,(
% 1.14/0.69    ! [X0] : k2_subset_1(X0) = X0),
% 1.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.14/0.69  fof(f31,plain,(
% 1.14/0.69    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.14/0.69    inference(cnf_transformation,[],[f24])).
% 1.14/0.69  fof(f65,plain,(
% 1.14/0.69    ~spl3_1 | ~spl3_2),
% 1.14/0.69    inference(avatar_split_clause,[],[f58,f63,f60])).
% 1.14/0.69  fof(f58,plain,(
% 1.14/0.69    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.14/0.69    inference(forward_demodulation,[],[f32,f35])).
% 1.14/0.69  fof(f32,plain,(
% 1.14/0.69    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.14/0.69    inference(cnf_transformation,[],[f24])).
% 1.14/0.69  % SZS output end Proof for theBenchmark
% 1.14/0.69  % (24231)------------------------------
% 1.14/0.69  % (24231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.69  % (24231)Termination reason: Refutation
% 1.14/0.69  
% 1.14/0.69  % (24231)Memory used [KB]: 10746
% 1.14/0.69  % (24231)Time elapsed: 0.104 s
% 1.14/0.69  % (24231)------------------------------
% 1.14/0.69  % (24231)------------------------------
% 1.14/0.69  % (24044)Success in time 0.33 s
%------------------------------------------------------------------------------
