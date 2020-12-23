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
% DateTime   : Thu Dec  3 12:44:39 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 325 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  262 ( 772 expanded)
%              Number of equality atoms :   77 ( 279 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f578,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f69,f91,f177,f185,f577])).

fof(f577,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f575])).

fof(f575,plain,
    ( sK0 != sK0
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f178,f504])).

fof(f504,plain,
    ( sK0 = sK1
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f187,f501])).

fof(f501,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f269,f499])).

fof(f499,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f498,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f498,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f497,f152])).

fof(f152,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f151,f135])).

fof(f135,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f132,f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(forward_demodulation,[],[f126,f36])).

fof(f126,plain,(
    ! [X1] : r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1) ),
    inference(superposition,[],[f73,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f151,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f146,f36])).

fof(f146,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[],[f54,f123])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f95,f39])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f497,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f496,f189])).

fof(f189,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f187,f39])).

fof(f496,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f468,f39])).

fof(f468,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f56,f189])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f53,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f269,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f226,f39])).

fof(f226,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f219,f47])).

fof(f219,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f73,f199])).

fof(f199,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f188,f198])).

fof(f198,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f179,f189])).

fof(f179,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f30,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f188,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f62,f47])).

fof(f62,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f187,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f186,f47])).

fof(f186,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f184,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f184,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f178,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(forward_demodulation,[],[f67,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f185,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f180,f182,f80])).

fof(f80,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f180,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
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

fof(f177,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f175,f34])).

fof(f175,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f72,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f173,f152])).

fof(f173,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f171,f135])).

fof(f171,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f71])).

fof(f71,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f30,f70])).

fof(f70,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f66,f35])).

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

fof(f91,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f82,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f69,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f31,f65,f61])).

fof(f31,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f65,f61])).

fof(f32,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31187)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (31200)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (31187)Refutation not found, incomplete strategy% (31187)------------------------------
% 0.21/0.51  % (31187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31182)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31179)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (31178)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (31178)Refutation not found, incomplete strategy% (31178)------------------------------
% 0.21/0.51  % (31178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31178)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31178)Memory used [KB]: 1663
% 0.21/0.51  % (31178)Time elapsed: 0.094 s
% 0.21/0.51  % (31178)------------------------------
% 0.21/0.51  % (31178)------------------------------
% 1.21/0.52  % (31184)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (31181)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (31187)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (31187)Memory used [KB]: 10618
% 1.21/0.52  % (31187)Time elapsed: 0.092 s
% 1.21/0.52  % (31187)------------------------------
% 1.21/0.52  % (31187)------------------------------
% 1.21/0.52  % (31197)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.52  % (31186)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.52  % (31188)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.52  % (31201)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  % (31201)Refutation not found, incomplete strategy% (31201)------------------------------
% 1.21/0.53  % (31201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (31201)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (31201)Memory used [KB]: 10746
% 1.21/0.53  % (31201)Time elapsed: 0.108 s
% 1.21/0.53  % (31201)------------------------------
% 1.21/0.53  % (31201)------------------------------
% 1.21/0.53  % (31196)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.53  % (31196)Refutation not found, incomplete strategy% (31196)------------------------------
% 1.21/0.53  % (31196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (31196)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (31196)Memory used [KB]: 10618
% 1.21/0.53  % (31196)Time elapsed: 0.099 s
% 1.21/0.53  % (31196)------------------------------
% 1.21/0.53  % (31196)------------------------------
% 1.21/0.53  % (31190)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.53  % (31192)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.53  % (31199)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.53  % (31189)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.54  % (31199)Refutation not found, incomplete strategy% (31199)------------------------------
% 1.21/0.54  % (31199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (31199)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (31199)Memory used [KB]: 10874
% 1.21/0.54  % (31199)Time elapsed: 0.122 s
% 1.21/0.54  % (31199)------------------------------
% 1.21/0.54  % (31199)------------------------------
% 1.35/0.54  % (31183)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (31206)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (31180)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (31185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (31188)Refutation not found, incomplete strategy% (31188)------------------------------
% 1.35/0.54  % (31188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (31188)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (31188)Memory used [KB]: 10618
% 1.35/0.54  % (31188)Time elapsed: 0.109 s
% 1.35/0.54  % (31188)------------------------------
% 1.35/0.54  % (31188)------------------------------
% 1.35/0.55  % (31189)Refutation not found, incomplete strategy% (31189)------------------------------
% 1.35/0.55  % (31189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (31191)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (31189)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (31189)Memory used [KB]: 10618
% 1.35/0.55  % (31189)Time elapsed: 0.133 s
% 1.35/0.55  % (31189)------------------------------
% 1.35/0.55  % (31189)------------------------------
% 1.35/0.55  % (31195)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.55  % (31203)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (31190)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f578,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f68,f69,f91,f177,f185,f577])).
% 1.35/0.55  fof(f577,plain,(
% 1.35/0.55    ~spl3_1 | spl3_2 | ~spl3_5),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f576])).
% 1.35/0.55  fof(f576,plain,(
% 1.35/0.55    $false | (~spl3_1 | spl3_2 | ~spl3_5)),
% 1.35/0.55    inference(trivial_inequality_removal,[],[f575])).
% 1.35/0.55  fof(f575,plain,(
% 1.35/0.55    sK0 != sK0 | (~spl3_1 | spl3_2 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f178,f504])).
% 1.35/0.55  fof(f504,plain,(
% 1.35/0.55    sK0 = sK1 | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(backward_demodulation,[],[f187,f501])).
% 1.35/0.55  fof(f501,plain,(
% 1.35/0.55    sK0 = k3_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(backward_demodulation,[],[f269,f499])).
% 1.35/0.55  fof(f499,plain,(
% 1.35/0.55    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.35/0.55    inference(forward_demodulation,[],[f498,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.35/0.55  fof(f498,plain,(
% 1.35/0.55    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.35/0.55    inference(forward_demodulation,[],[f497,f152])).
% 1.35/0.55  fof(f152,plain,(
% 1.35/0.55    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f151,f135])).
% 1.35/0.55  fof(f135,plain,(
% 1.35/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.35/0.55    inference(resolution,[],[f132,f47])).
% 1.35/0.55  fof(f47,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f19])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.55  fof(f132,plain,(
% 1.35/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f126,f36])).
% 1.35/0.55  fof(f126,plain,(
% 1.35/0.55    ( ! [X1] : (r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1)) )),
% 1.35/0.55    inference(superposition,[],[f73,f95])).
% 1.35/0.55  fof(f95,plain,(
% 1.35/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(resolution,[],[f47,f34])).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.55  fof(f73,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 1.35/0.55    inference(superposition,[],[f55,f39])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.55  fof(f55,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f37,f42])).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.35/0.55  fof(f151,plain,(
% 1.35/0.55    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 1.35/0.55    inference(forward_demodulation,[],[f146,f36])).
% 1.35/0.55  fof(f146,plain,(
% 1.35/0.55    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)))) )),
% 1.35/0.55    inference(superposition,[],[f54,f123])).
% 1.35/0.55  fof(f123,plain,(
% 1.35/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.35/0.55    inference(superposition,[],[f95,f39])).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.35/0.55    inference(definition_unfolding,[],[f41,f42,f42])).
% 1.35/0.55  fof(f41,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.35/0.55  fof(f497,plain,(
% 1.35/0.55    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | ~spl3_5),
% 1.35/0.55    inference(forward_demodulation,[],[f496,f189])).
% 1.35/0.55  fof(f189,plain,(
% 1.35/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 1.35/0.55    inference(superposition,[],[f187,f39])).
% 1.35/0.55  fof(f496,plain,(
% 1.35/0.55    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.35/0.55    inference(forward_demodulation,[],[f468,f39])).
% 1.35/0.55  fof(f468,plain,(
% 1.35/0.55    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl3_5),
% 1.35/0.55    inference(superposition,[],[f56,f189])).
% 1.35/0.55  fof(f56,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.35/0.55    inference(definition_unfolding,[],[f38,f53,f53])).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.35/0.55    inference(definition_unfolding,[],[f40,f42])).
% 1.35/0.55  fof(f40,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.35/0.55  fof(f38,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.35/0.55  fof(f269,plain,(
% 1.35/0.55    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f226,f39])).
% 1.35/0.55  fof(f226,plain,(
% 1.35/0.55    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(resolution,[],[f219,f47])).
% 1.35/0.55  fof(f219,plain,(
% 1.35/0.55    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(superposition,[],[f73,f199])).
% 1.35/0.55  fof(f199,plain,(
% 1.35/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | (~spl3_1 | ~spl3_5)),
% 1.35/0.55    inference(backward_demodulation,[],[f188,f198])).
% 1.35/0.55  fof(f198,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_5),
% 1.35/0.55    inference(backward_demodulation,[],[f179,f189])).
% 1.35/0.55  fof(f179,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.35/0.55    inference(resolution,[],[f30,f57])).
% 1.35/0.55  fof(f57,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f48,f42])).
% 1.35/0.55  fof(f48,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,axiom,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(flattening,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f17])).
% 1.35/0.55  fof(f17,plain,(
% 1.35/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.35/0.55    inference(negated_conjecture,[],[f15])).
% 1.35/0.55  fof(f15,conjecture,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.35/0.55  fof(f188,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.35/0.55    inference(resolution,[],[f62,f47])).
% 1.35/0.55  fof(f62,plain,(
% 1.35/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f61])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.35/0.55  fof(f187,plain,(
% 1.35/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 1.35/0.55    inference(resolution,[],[f186,f47])).
% 1.35/0.55  fof(f186,plain,(
% 1.35/0.55    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.35/0.55    inference(resolution,[],[f184,f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.35/0.55    inference(equality_resolution,[],[f49])).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(rectify,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.35/0.55  fof(f184,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.35/0.55    inference(avatar_component_clause,[],[f182])).
% 1.35/0.55  fof(f182,plain,(
% 1.35/0.55    spl3_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.35/0.55  fof(f178,plain,(
% 1.35/0.55    sK0 != sK1 | spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f67,f35])).
% 1.35/0.55  fof(f35,plain,(
% 1.35/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,axiom,(
% 1.35/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.55  fof(f67,plain,(
% 1.35/0.55    sK1 != k2_subset_1(sK0) | spl3_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f65])).
% 1.35/0.55  fof(f65,plain,(
% 1.35/0.55    spl3_2 <=> sK1 = k2_subset_1(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.35/0.55  fof(f185,plain,(
% 1.35/0.55    spl3_3 | spl3_5),
% 1.35/0.55    inference(avatar_split_clause,[],[f180,f182,f80])).
% 1.35/0.55  fof(f80,plain,(
% 1.35/0.55    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.35/0.55  fof(f180,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(resolution,[],[f30,f43])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,plain,(
% 1.35/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f11])).
% 1.35/0.55  fof(f11,axiom,(
% 1.35/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.35/0.55  fof(f177,plain,(
% 1.35/0.55    spl3_1 | ~spl3_2),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 1.35/0.55  fof(f176,plain,(
% 1.35/0.55    $false | (spl3_1 | ~spl3_2)),
% 1.35/0.55    inference(resolution,[],[f175,f34])).
% 1.35/0.55  fof(f175,plain,(
% 1.35/0.55    ~r1_tarski(k1_xboole_0,sK0) | (spl3_1 | ~spl3_2)),
% 1.35/0.55    inference(backward_demodulation,[],[f72,f174])).
% 1.35/0.55  fof(f174,plain,(
% 1.35/0.55    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f173,f152])).
% 1.35/0.55  fof(f173,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) | ~spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f171,f135])).
% 1.35/0.55  fof(f171,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl3_2),
% 1.35/0.55    inference(resolution,[],[f57,f71])).
% 1.35/0.55  fof(f71,plain,(
% 1.35/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.35/0.55    inference(backward_demodulation,[],[f30,f70])).
% 1.35/0.55  fof(f70,plain,(
% 1.35/0.55    sK0 = sK1 | ~spl3_2),
% 1.35/0.55    inference(forward_demodulation,[],[f66,f35])).
% 1.35/0.55  fof(f66,plain,(
% 1.35/0.55    sK1 = k2_subset_1(sK0) | ~spl3_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f65])).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 1.35/0.55    inference(forward_demodulation,[],[f63,f70])).
% 1.35/0.55  fof(f63,plain,(
% 1.35/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f61])).
% 1.35/0.55  fof(f91,plain,(
% 1.35/0.55    ~spl3_3),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f88])).
% 1.35/0.55  fof(f88,plain,(
% 1.35/0.55    $false | ~spl3_3),
% 1.35/0.55    inference(resolution,[],[f82,f33])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f14])).
% 1.35/0.55  fof(f14,axiom,(
% 1.35/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.35/0.55  fof(f82,plain,(
% 1.35/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.35/0.55    inference(avatar_component_clause,[],[f80])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    spl3_1 | spl3_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f31,f65,f61])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  fof(f68,plain,(
% 1.35/0.55    ~spl3_1 | ~spl3_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f32,f65,f61])).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (31190)------------------------------
% 1.35/0.55  % (31190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (31190)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (31190)Memory used [KB]: 6396
% 1.35/0.55  % (31190)Time elapsed: 0.124 s
% 1.35/0.55  % (31190)------------------------------
% 1.35/0.55  % (31190)------------------------------
% 1.35/0.55  % (31198)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (31174)Success in time 0.183 s
%------------------------------------------------------------------------------
