%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:50 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 572 expanded)
%              Number of leaves         :   21 ( 179 expanded)
%              Depth                    :   22
%              Number of atoms          :  198 (1237 expanded)
%              Number of equality atoms :   72 ( 509 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f388,f391,f522])).

fof(f522,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( sK0 != sK0
    | ~ spl3_5 ),
    inference(superposition,[],[f363,f515])).

fof(f515,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f507,f366])).

fof(f366,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f359,f360])).

fof(f360,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f91,f354])).

fof(f354,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f352,f159])).

fof(f159,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(resolution,[],[f117,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f80,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_tarski(k1_enumset1(X2,X2,X3)) = X3 ) ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f352,plain,(
    sK1 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f346,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f346,plain,(
    sK1 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f120,f166])).

fof(f166,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f164,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f164,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f75,f162])).

fof(f162,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f158,f60])).

fof(f158,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f117,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) ),
    inference(superposition,[],[f61,f60])).

fof(f61,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f120,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[],[f63,f40])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f46,f59,f45])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f91,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f65,f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f359,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f127,f354])).

fof(f127,plain,(
    sK0 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f63,f91])).

fof(f507,plain,
    ( k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(resolution,[],[f394,f34])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(sK0,sK1))) )
    | ~ spl3_5 ),
    inference(resolution,[],[f387,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f387,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl3_5
  <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f363,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f69,f360])).

fof(f69,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f35,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f391,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f383,f34])).

fof(f383,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f388,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f379,f385,f381])).

fof(f379,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f52,f360])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.52  % (12518)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12532)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (12524)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (12533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (12508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (12511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.56  % (12510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.57  % (12507)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.57  % (12527)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.57  % (12517)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (12525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.58  % (12515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.58  % (12518)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f523,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(avatar_sat_refutation,[],[f388,f391,f522])).
% 1.50/0.58  fof(f522,plain,(
% 1.50/0.58    ~spl3_5),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f521])).
% 1.50/0.58  fof(f521,plain,(
% 1.50/0.58    $false | ~spl3_5),
% 1.50/0.58    inference(trivial_inequality_removal,[],[f520])).
% 1.50/0.58  fof(f520,plain,(
% 1.50/0.58    sK0 != sK0 | ~spl3_5),
% 1.50/0.58    inference(superposition,[],[f363,f515])).
% 1.50/0.58  fof(f515,plain,(
% 1.50/0.58    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.50/0.58    inference(forward_demodulation,[],[f507,f366])).
% 1.50/0.58  fof(f366,plain,(
% 1.50/0.58    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 1.50/0.58    inference(backward_demodulation,[],[f359,f360])).
% 1.50/0.58  fof(f360,plain,(
% 1.50/0.58    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.50/0.58    inference(backward_demodulation,[],[f91,f354])).
% 1.50/0.58  fof(f354,plain,(
% 1.50/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 1.50/0.58    inference(superposition,[],[f352,f159])).
% 1.50/0.58  fof(f159,plain,(
% 1.50/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.50/0.58    inference(resolution,[],[f117,f38])).
% 1.50/0.58  fof(f38,plain,(
% 1.50/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f17])).
% 1.50/0.58  fof(f17,axiom,(
% 1.50/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.50/0.58  fof(f117,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.50/0.58    inference(resolution,[],[f80,f36])).
% 1.50/0.58  fof(f36,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f15])).
% 1.50/0.58  fof(f15,axiom,(
% 1.50/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.50/0.58  fof(f80,plain,(
% 1.50/0.58    ( ! [X2,X3] : (v1_xboole_0(k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k1_enumset1(X2,X2,X3)) = X3) )),
% 1.50/0.58    inference(resolution,[],[f74,f47])).
% 1.50/0.58  fof(f47,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f29])).
% 1.50/0.58  fof(f29,plain,(
% 1.50/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.50/0.58    inference(nnf_transformation,[],[f21])).
% 1.50/0.58  fof(f21,plain,(
% 1.50/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.50/0.58  fof(f74,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.50/0.58    inference(resolution,[],[f64,f68])).
% 1.50/0.58  fof(f68,plain,(
% 1.50/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.50/0.58    inference(equality_resolution,[],[f54])).
% 1.50/0.58  fof(f54,plain,(
% 1.50/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f33])).
% 1.50/0.58  fof(f33,plain,(
% 1.50/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.50/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.50/0.58    inference(rectify,[],[f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.50/0.58    inference(nnf_transformation,[],[f9])).
% 1.50/0.58  fof(f9,axiom,(
% 1.50/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.50/0.58  fof(f64,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.50/0.58    inference(definition_unfolding,[],[f51,f59])).
% 1.50/0.58  fof(f59,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f44,f43])).
% 1.50/0.58  fof(f43,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f8])).
% 1.50/0.58  fof(f8,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.58  fof(f44,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f10])).
% 1.50/0.58  fof(f10,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.58  fof(f51,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f22])).
% 1.50/0.58  fof(f22,plain,(
% 1.50/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f3])).
% 1.50/0.58  fof(f3,axiom,(
% 1.50/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.50/0.58  fof(f352,plain,(
% 1.50/0.58    sK1 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_xboole_0(sK0,sK1)))),
% 1.50/0.58    inference(forward_demodulation,[],[f346,f60])).
% 1.50/0.58  fof(f60,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f39,f43,f43])).
% 1.50/0.58  fof(f39,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.50/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.50/0.58  fof(f346,plain,(
% 1.50/0.58    sK1 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k1_xboole_0))),
% 1.50/0.58    inference(superposition,[],[f120,f166])).
% 1.50/0.58  fof(f166,plain,(
% 1.50/0.58    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 1.50/0.58    inference(forward_demodulation,[],[f164,f40])).
% 1.78/0.58  fof(f40,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f1])).
% 1.78/0.58  fof(f1,axiom,(
% 1.78/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.78/0.58  fof(f164,plain,(
% 1.78/0.58    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 1.78/0.58    inference(superposition,[],[f75,f162])).
% 1.78/0.58  fof(f162,plain,(
% 1.78/0.58    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f158,f60])).
% 1.78/0.58  fof(f158,plain,(
% 1.78/0.58    sK0 = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 1.78/0.58    inference(resolution,[],[f117,f34])).
% 1.78/0.58  fof(f34,plain,(
% 1.78/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.78/0.58    inference(cnf_transformation,[],[f28])).
% 1.78/0.58  fof(f28,plain,(
% 1.78/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.78/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f27])).
% 1.78/0.58  fof(f27,plain,(
% 1.78/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.78/0.58    introduced(choice_axiom,[])).
% 1.78/0.58  fof(f20,plain,(
% 1.78/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f19])).
% 1.78/0.58  fof(f19,negated_conjecture,(
% 1.78/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.78/0.58    inference(negated_conjecture,[],[f18])).
% 1.78/0.58  fof(f18,conjecture,(
% 1.78/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.78/0.58  fof(f75,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))))) )),
% 1.78/0.58    inference(superposition,[],[f61,f60])).
% 1.78/0.58  fof(f61,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))))) )),
% 1.78/0.58    inference(definition_unfolding,[],[f41,f45,f59])).
% 1.78/0.58  fof(f45,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f2])).
% 1.78/0.58  fof(f2,axiom,(
% 1.78/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.78/0.58  fof(f41,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.78/0.58    inference(cnf_transformation,[],[f5])).
% 1.78/0.58  fof(f5,axiom,(
% 1.78/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.78/0.58  fof(f120,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0) )),
% 1.78/0.58    inference(superposition,[],[f63,f40])).
% 1.78/0.58  fof(f63,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 1.78/0.58    inference(definition_unfolding,[],[f46,f59,f45])).
% 1.78/0.58  fof(f46,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.78/0.58    inference(cnf_transformation,[],[f6])).
% 1.78/0.58  fof(f6,axiom,(
% 1.78/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.78/0.58  fof(f91,plain,(
% 1.78/0.58    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f65,f34])).
% 1.78/0.58  fof(f65,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.78/0.58    inference(definition_unfolding,[],[f53,f45])).
% 1.78/0.58  fof(f53,plain,(
% 1.78/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f24,plain,(
% 1.78/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f13])).
% 1.78/0.58  fof(f13,axiom,(
% 1.78/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.78/0.58  fof(f359,plain,(
% 1.78/0.58    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.78/0.58    inference(backward_demodulation,[],[f127,f354])).
% 1.78/0.58  fof(f127,plain,(
% 1.78/0.58    sK0 = k3_tarski(k1_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)))),
% 1.78/0.58    inference(superposition,[],[f63,f91])).
% 1.78/0.58  fof(f507,plain,(
% 1.78/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.78/0.58    inference(resolution,[],[f394,f34])).
% 1.78/0.58  fof(f394,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(sK0,sK1)))) ) | ~spl3_5),
% 1.78/0.58    inference(resolution,[],[f387,f66])).
% 1.78/0.58  fof(f66,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.78/0.58    inference(definition_unfolding,[],[f58,f59])).
% 1.78/0.58  fof(f58,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f26])).
% 1.78/0.58  fof(f26,plain,(
% 1.78/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(flattening,[],[f25])).
% 1.78/0.58  fof(f25,plain,(
% 1.78/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.78/0.58    inference(ennf_transformation,[],[f16])).
% 1.78/0.58  fof(f16,axiom,(
% 1.78/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.78/0.58  fof(f387,plain,(
% 1.78/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.78/0.58    inference(avatar_component_clause,[],[f385])).
% 1.78/0.58  fof(f385,plain,(
% 1.78/0.58    spl3_5 <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.78/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.78/0.58  fof(f363,plain,(
% 1.78/0.58    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.78/0.58    inference(backward_demodulation,[],[f69,f360])).
% 1.78/0.58  fof(f69,plain,(
% 1.78/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.78/0.58    inference(backward_demodulation,[],[f35,f37])).
% 1.78/0.58  fof(f37,plain,(
% 1.78/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.78/0.58    inference(cnf_transformation,[],[f12])).
% 1.78/0.58  fof(f12,axiom,(
% 1.78/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.78/0.58  fof(f35,plain,(
% 1.78/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.78/0.58    inference(cnf_transformation,[],[f28])).
% 1.78/0.58  fof(f391,plain,(
% 1.78/0.58    spl3_4),
% 1.78/0.58    inference(avatar_contradiction_clause,[],[f389])).
% 1.78/0.58  fof(f389,plain,(
% 1.78/0.58    $false | spl3_4),
% 1.78/0.58    inference(resolution,[],[f383,f34])).
% 1.78/0.58  fof(f383,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_4),
% 1.78/0.58    inference(avatar_component_clause,[],[f381])).
% 1.78/0.58  fof(f381,plain,(
% 1.78/0.58    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.78/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.78/0.58  fof(f388,plain,(
% 1.78/0.58    ~spl3_4 | spl3_5),
% 1.78/0.58    inference(avatar_split_clause,[],[f379,f385,f381])).
% 1.78/0.58  fof(f379,plain,(
% 1.78/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.78/0.58    inference(superposition,[],[f52,f360])).
% 1.78/0.58  fof(f52,plain,(
% 1.78/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f23])).
% 1.78/0.58  fof(f23,plain,(
% 1.78/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f14])).
% 1.78/0.58  fof(f14,axiom,(
% 1.78/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.78/0.58  % SZS output end Proof for theBenchmark
% 1.78/0.58  % (12518)------------------------------
% 1.78/0.58  % (12518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.58  % (12518)Termination reason: Refutation
% 1.78/0.58  
% 1.78/0.58  % (12518)Memory used [KB]: 6524
% 1.78/0.58  % (12518)Time elapsed: 0.147 s
% 1.78/0.58  % (12518)------------------------------
% 1.78/0.58  % (12518)------------------------------
% 1.78/0.58  % (12519)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.78/0.58  % (12530)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.78/0.58  % (12505)Success in time 0.222 s
%------------------------------------------------------------------------------
