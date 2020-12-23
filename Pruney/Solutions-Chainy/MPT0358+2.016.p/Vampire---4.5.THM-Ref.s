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
% DateTime   : Thu Dec  3 12:44:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 411 expanded)
%              Number of leaves         :   22 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          :  409 (1649 expanded)
%              Number of equality atoms :   72 ( 325 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f102,f105,f211,f409,f532])).

fof(f532,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f86,f504])).

fof(f504,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(superposition,[],[f358,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f358,plain,
    ( ! [X1] : k2_xboole_0(sK1,X1) = X1
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f339,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f339,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f334,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f334,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f287,f269])).

fof(f269,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f88,f265])).

fof(f265,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f212,f230])).

fof(f230,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f225,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f225,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f219,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f219,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f217,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f217,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_7
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f212,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f39,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f88,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k5_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_7 ),
    inference(resolution,[],[f274,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f274,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f228,f265])).

fof(f228,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f79,f212])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f46])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f409,plain,
    ( spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f407,f216,f97])).

fof(f97,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f407,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f211,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f113,f202])).

fof(f202,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl5_4 ),
    inference(resolution,[],[f192,f55])).

fof(f192,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f188,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f135,f44])).

fof(f135,plain,
    ( k1_xboole_0 = k2_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f115,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0),X2),k1_xboole_0)
        | r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f110,f55])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f80,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f106,f52])).

fof(f106,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f101,f77])).

fof(f101,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_4
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f46])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f79,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f159,f52])).

fof(f159,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f133,f146])).

fof(f113,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f103,f109])).

fof(f109,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f95,f107])).

fof(f95,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f92,f45])).

fof(f92,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f69])).

fof(f91,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f39,f89])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f103,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f83,f89])).

fof(f83,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f105,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f98,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f102,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f93,f85,f100,f97])).

fof(f93,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f47])).

fof(f90,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f68,f85,f82])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f40,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f85,f82])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (20118)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (20126)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (20118)Refutation not found, incomplete strategy% (20118)------------------------------
% 0.21/0.51  % (20118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20118)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20118)Memory used [KB]: 10618
% 0.21/0.51  % (20118)Time elapsed: 0.102 s
% 0.21/0.51  % (20118)------------------------------
% 0.21/0.51  % (20118)------------------------------
% 0.21/0.51  % (20116)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (20124)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (20134)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (20115)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (20114)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (20110)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20109)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (20130)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (20132)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (20111)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (20130)Refutation not found, incomplete strategy% (20130)------------------------------
% 0.21/0.53  % (20130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20120)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20130)Memory used [KB]: 10746
% 0.21/0.53  % (20130)Time elapsed: 0.079 s
% 0.21/0.53  % (20130)------------------------------
% 0.21/0.53  % (20130)------------------------------
% 0.21/0.53  % (20112)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (20122)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (20125)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (20137)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (20113)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (20136)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (20108)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (20127)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (20128)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20117)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20129)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (20119)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (20119)Refutation not found, incomplete strategy% (20119)------------------------------
% 0.21/0.55  % (20119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20119)Memory used [KB]: 10618
% 0.21/0.55  % (20119)Time elapsed: 0.149 s
% 0.21/0.55  % (20119)------------------------------
% 0.21/0.55  % (20119)------------------------------
% 0.21/0.55  % (20121)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (20110)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f536,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f87,f90,f102,f105,f211,f409,f532])).
% 0.21/0.55  fof(f532,plain,(
% 0.21/0.55    ~spl5_1 | spl5_2 | ~spl5_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f506])).
% 0.21/0.55  fof(f506,plain,(
% 0.21/0.55    $false | (~spl5_1 | spl5_2 | ~spl5_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f86,f504])).
% 0.21/0.55  fof(f504,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(superposition,[],[f358,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.55  fof(f358,plain,(
% 0.21/0.55    ( ! [X1] : (k2_xboole_0(sK1,X1) = X1) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(resolution,[],[f339,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(sK1,X2)) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(resolution,[],[f334,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f334,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f333])).
% 0.21/0.55  fof(f333,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK1)) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(resolution,[],[f287,f269])).
% 0.21/0.55  fof(f269,plain,(
% 0.21/0.55    r1_tarski(sK1,k5_xboole_0(sK0,sK1)) | (~spl5_1 | ~spl5_7)),
% 0.21/0.55    inference(backward_demodulation,[],[f88,f265])).
% 0.21/0.55  fof(f265,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl5_7),
% 0.21/0.55    inference(backward_demodulation,[],[f212,f230])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl5_7),
% 0.21/0.55    inference(superposition,[],[f225,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl5_7),
% 0.21/0.55    inference(resolution,[],[f219,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | ~spl5_7),
% 0.21/0.55    inference(resolution,[],[f217,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f216])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    spl5_7 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(resolution,[],[f39,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f13])).
% 0.21/0.55  fof(f13,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl5_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,sK1)) ) | ~spl5_7),
% 0.21/0.55    inference(resolution,[],[f274,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl5_7),
% 0.21/0.55    inference(backward_demodulation,[],[f228,f265])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.55    inference(superposition,[],[f79,f212])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f62,f46])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    spl5_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f409,plain,(
% 0.21/0.55    spl5_3 | spl5_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f407,f216,f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl5_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f39,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    spl5_1 | ~spl5_2 | ~spl5_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    $false | (spl5_1 | ~spl5_2 | ~spl5_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f202])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl5_4),
% 0.21/0.55    inference(resolution,[],[f192,f55])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_4),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_4),
% 0.21/0.55    inference(forward_demodulation,[],[f188,f146])).
% 0.21/0.55  fof(f146,plain,(
% 1.48/0.55    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(superposition,[],[f135,f44])).
% 1.48/0.55  fof(f135,plain,(
% 1.48/0.55    k1_xboole_0 = k2_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f133,f51])).
% 1.48/0.55  fof(f133,plain,(
% 1.48/0.55    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f132])).
% 1.48/0.55  fof(f132,plain,(
% 1.48/0.55    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f115,f56])).
% 1.48/0.55  fof(f56,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f29])).
% 1.48/0.55  fof(f115,plain,(
% 1.48/0.55    ( ! [X2] : (r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0),X2),k1_xboole_0) | r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X2)) ) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f110,f55])).
% 1.48/0.55  fof(f110,plain,(
% 1.48/0.55    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl5_4),
% 1.48/0.55    inference(superposition,[],[f80,f107])).
% 1.48/0.55  fof(f107,plain,(
% 1.48/0.55    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f106,f52])).
% 1.48/0.55  fof(f106,plain,(
% 1.48/0.55    r1_tarski(k1_xboole_0,sK0) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f101,f77])).
% 1.48/0.55  fof(f101,plain,(
% 1.48/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.48/0.55    inference(avatar_component_clause,[],[f100])).
% 1.48/0.55  fof(f100,plain,(
% 1.48/0.55    spl5_4 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.48/0.55    inference(equality_resolution,[],[f75])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.48/0.55    inference(definition_unfolding,[],[f61,f46])).
% 1.48/0.55  fof(f61,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f38])).
% 1.48/0.55  fof(f188,plain,(
% 1.48/0.55    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_4),
% 1.48/0.55    inference(superposition,[],[f79,f177])).
% 1.48/0.55  fof(f177,plain,(
% 1.48/0.55    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(resolution,[],[f159,f52])).
% 1.48/0.55  fof(f159,plain,(
% 1.48/0.55    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_4),
% 1.48/0.55    inference(backward_demodulation,[],[f133,f146])).
% 1.48/0.55  fof(f113,plain,(
% 1.48/0.55    ~r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) | (spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.48/0.55    inference(backward_demodulation,[],[f103,f109])).
% 1.48/0.55  fof(f109,plain,(
% 1.48/0.55    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 1.48/0.55    inference(backward_demodulation,[],[f95,f107])).
% 1.48/0.55  fof(f95,plain,(
% 1.48/0.55    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0)) | ~spl5_2),
% 1.48/0.55    inference(forward_demodulation,[],[f92,f45])).
% 1.48/0.55  fof(f92,plain,(
% 1.48/0.55    k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) = k3_subset_1(sK0,k1_xboole_0) | ~spl5_2),
% 1.48/0.55    inference(resolution,[],[f91,f69])).
% 1.48/0.55  fof(f91,plain,(
% 1.48/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.48/0.55    inference(forward_demodulation,[],[f39,f89])).
% 1.48/0.55  fof(f89,plain,(
% 1.48/0.55    k1_xboole_0 = sK1 | ~spl5_2),
% 1.48/0.55    inference(avatar_component_clause,[],[f85])).
% 1.48/0.55  fof(f103,plain,(
% 1.48/0.55    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (spl5_1 | ~spl5_2)),
% 1.48/0.55    inference(forward_demodulation,[],[f83,f89])).
% 1.48/0.55  fof(f83,plain,(
% 1.48/0.55    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl5_1),
% 1.48/0.55    inference(avatar_component_clause,[],[f82])).
% 1.48/0.55  fof(f105,plain,(
% 1.48/0.55    ~spl5_3),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f104])).
% 1.48/0.55  fof(f104,plain,(
% 1.48/0.55    $false | ~spl5_3),
% 1.48/0.55    inference(resolution,[],[f98,f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f12])).
% 1.48/0.55  fof(f12,axiom,(
% 1.48/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.48/0.55  fof(f98,plain,(
% 1.48/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_3),
% 1.48/0.55    inference(avatar_component_clause,[],[f97])).
% 1.48/0.55  fof(f102,plain,(
% 1.48/0.55    spl5_3 | spl5_4 | ~spl5_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f93,f85,f100,f97])).
% 1.48/0.55  fof(f93,plain,(
% 1.48/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.48/0.55    inference(resolution,[],[f91,f47])).
% 1.48/0.55  fof(f90,plain,(
% 1.48/0.55    spl5_1 | spl5_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f68,f85,f82])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.48/0.55    inference(definition_unfolding,[],[f40,f43])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f10])).
% 1.48/0.55  fof(f10,axiom,(
% 1.48/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.48/0.55    inference(cnf_transformation,[],[f24])).
% 1.48/0.55  fof(f87,plain,(
% 1.48/0.55    ~spl5_1 | ~spl5_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f67,f85,f82])).
% 1.48/0.55  fof(f67,plain,(
% 1.48/0.55    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.48/0.55    inference(definition_unfolding,[],[f41,f43])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.48/0.55    inference(cnf_transformation,[],[f24])).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (20110)------------------------------
% 1.48/0.55  % (20110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (20110)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (20110)Memory used [KB]: 10874
% 1.48/0.55  % (20110)Time elapsed: 0.149 s
% 1.48/0.55  % (20110)------------------------------
% 1.48/0.55  % (20110)------------------------------
% 1.48/0.55  % (20107)Success in time 0.192 s
%------------------------------------------------------------------------------
