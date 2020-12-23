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
% DateTime   : Thu Dec  3 12:44:12 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 125 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 ( 286 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f172,f43,f83,f94,f136])).

fof(f136,plain,(
    ! [X6,X4,X5] :
      ( k4_subset_1(X6,X4,X5) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f94,plain,(
    sK2 != k4_subset_1(sK2,sK3,sK2) ),
    inference(forward_demodulation,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f44,plain,(
    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f46])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f172,plain,(
    r1_tarski(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( r1_tarski(sK3,sK2)
    | r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f151,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK2)
      | r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f145,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f110,f117])).

fof(f117,plain,(
    ! [X5] :
      ( sP0(k1_zfmisc_1(sK2),X5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(resolution,[],[f64,f98])).

fof(f98,plain,(
    r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f95,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP0(X0,X1)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ( r2_hidden(sK6(X0,X1),X0)
          & r2_hidden(X1,sK6(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X1,X3) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(X1,sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X1,X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2] :
      ( ( sP0(X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X2,X3) )
        | ~ sP0(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2] :
      ( sP0(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ sP0(k1_zfmisc_1(X2),X3)
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f59,f82])).

fof(f82,plain,(
    ! [X0] : sP1(k1_zfmisc_1(X0),X0) ),
    inference(superposition,[],[f81,f47])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f81,plain,(
    ! [X0] : sP1(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f9,f27,f26])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X0,X3)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(X0,sK5(X0,X1))
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sP0(X0,sK5(X0,X1))
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X0,X2)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X0,X2)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(X0,sK5(X0,X1))
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sP0(X0,sK5(X0,X1))
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X0,X2) )
            & ( sP0(X0,X2)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (24643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (24660)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (24632)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (24650)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (24650)Refutation not found, incomplete strategy% (24650)------------------------------
% 0.21/0.58  % (24650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (24637)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.59  % (24650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (24650)Memory used [KB]: 10746
% 0.21/0.59  % (24650)Time elapsed: 0.166 s
% 0.21/0.59  % (24650)------------------------------
% 0.21/0.59  % (24650)------------------------------
% 0.21/0.59  % (24652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (24633)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (24644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.77/0.60  % (24634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.77/0.60  % (24647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.77/0.60  % (24647)Refutation not found, incomplete strategy% (24647)------------------------------
% 1.77/0.60  % (24647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (24647)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.60  
% 1.77/0.60  % (24647)Memory used [KB]: 10618
% 1.77/0.60  % (24647)Time elapsed: 0.173 s
% 1.77/0.60  % (24647)------------------------------
% 1.77/0.60  % (24647)------------------------------
% 1.77/0.60  % (24655)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.77/0.60  % (24640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.89/0.61  % (24652)Refutation not found, incomplete strategy% (24652)------------------------------
% 1.89/0.61  % (24652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (24652)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (24652)Memory used [KB]: 10618
% 1.89/0.61  % (24652)Time elapsed: 0.169 s
% 1.89/0.61  % (24652)------------------------------
% 1.89/0.61  % (24652)------------------------------
% 1.89/0.61  % (24640)Refutation not found, incomplete strategy% (24640)------------------------------
% 1.89/0.61  % (24640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (24661)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.89/0.61  % (24651)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.89/0.62  % (24661)Refutation found. Thanks to Tanya!
% 1.89/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.62  % (24651)Refutation not found, incomplete strategy% (24651)------------------------------
% 1.89/0.62  % (24651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (24651)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (24651)Memory used [KB]: 1663
% 1.89/0.62  % (24651)Time elapsed: 0.176 s
% 1.89/0.62  % (24651)------------------------------
% 1.89/0.62  % (24651)------------------------------
% 1.89/0.62  % (24638)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f176,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(unit_resulting_resolution,[],[f172,f43,f83,f94,f136])).
% 1.89/0.62  fof(f136,plain,(
% 1.89/0.62    ( ! [X6,X4,X5] : (k4_subset_1(X6,X4,X5) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~r1_tarski(X4,X5)) )),
% 1.89/0.62    inference(superposition,[],[f80,f79])).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f55,f78])).
% 1.89/0.62  fof(f78,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.89/0.62    inference(definition_unfolding,[],[f49,f77])).
% 1.89/0.62  fof(f77,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f50,f76])).
% 1.89/0.62  fof(f76,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f67,f75])).
% 1.89/0.62  fof(f75,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f69,f74])).
% 1.89/0.62  fof(f74,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f70,f73])).
% 1.89/0.62  fof(f73,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.62    inference(definition_unfolding,[],[f71,f72])).
% 1.89/0.62  fof(f72,plain,(
% 1.89/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f8])).
% 1.89/0.62  fof(f8,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.89/0.62  fof(f71,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f7])).
% 1.89/0.62  fof(f7,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.89/0.62  fof(f70,plain,(
% 1.89/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f6])).
% 1.89/0.62  fof(f6,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.89/0.62  fof(f69,plain,(
% 1.89/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f5])).
% 1.89/0.62  fof(f5,axiom,(
% 1.89/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.89/0.62  fof(f67,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f4])).
% 1.89/0.62  fof(f4,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.89/0.62  fof(f50,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f3])).
% 1.89/0.62  fof(f3,axiom,(
% 1.89/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.89/0.62  fof(f55,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f22])).
% 1.89/0.62  fof(f22,plain,(
% 1.89/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f2])).
% 1.89/0.62  fof(f2,axiom,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.89/0.62  fof(f80,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(definition_unfolding,[],[f68,f78])).
% 1.89/0.62  fof(f68,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f25])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(flattening,[],[f24])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.89/0.62    inference(ennf_transformation,[],[f16])).
% 1.89/0.62  fof(f16,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.89/0.62  fof(f94,plain,(
% 1.89/0.62    sK2 != k4_subset_1(sK2,sK3,sK2)),
% 1.89/0.62    inference(forward_demodulation,[],[f44,f46])).
% 1.89/0.62  fof(f46,plain,(
% 1.89/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.89/0.62    inference(cnf_transformation,[],[f13])).
% 1.89/0.62  fof(f13,axiom,(
% 1.89/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.89/0.62  fof(f44,plain,(
% 1.89/0.62    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))),
% 1.89/0.62    inference(cnf_transformation,[],[f30])).
% 1.89/0.62  fof(f30,plain,(
% 1.89/0.62    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f29])).
% 1.89/0.62  fof(f29,plain,(
% 1.89/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f20,plain,(
% 1.89/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f18])).
% 1.89/0.62  fof(f18,negated_conjecture,(
% 1.89/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.89/0.62    inference(negated_conjecture,[],[f17])).
% 1.89/0.62  fof(f17,conjecture,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.89/0.62  fof(f83,plain,(
% 1.89/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(forward_demodulation,[],[f48,f46])).
% 1.89/0.62  fof(f48,plain,(
% 1.89/0.62    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f14])).
% 1.89/0.62  fof(f14,axiom,(
% 1.89/0.62    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.89/0.62  fof(f43,plain,(
% 1.89/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 1.89/0.62    inference(cnf_transformation,[],[f30])).
% 1.89/0.62  fof(f172,plain,(
% 1.89/0.62    r1_tarski(sK3,sK2)),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f169])).
% 1.89/0.62  fof(f169,plain,(
% 1.89/0.62    r1_tarski(sK3,sK2) | r1_tarski(sK3,sK2)),
% 1.89/0.62    inference(resolution,[],[f151,f57])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f33])).
% 1.89/0.62  fof(f33,plain,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f23,plain,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,plain,(
% 1.89/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.89/0.62    inference(unused_predicate_definition_removal,[],[f1])).
% 1.89/0.62  fof(f1,axiom,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.89/0.62  fof(f151,plain,(
% 1.89/0.62    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK2) | r1_tarski(sK3,X0)) )),
% 1.89/0.62    inference(resolution,[],[f145,f56])).
% 1.89/0.62  fof(f56,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f33])).
% 1.89/0.62  fof(f145,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK2)) )),
% 1.89/0.62    inference(resolution,[],[f110,f117])).
% 1.89/0.62  fof(f117,plain,(
% 1.89/0.62    ( ! [X5] : (sP0(k1_zfmisc_1(sK2),X5) | ~r2_hidden(X5,sK3)) )),
% 1.89/0.62    inference(resolution,[],[f64,f98])).
% 1.89/0.62  fof(f98,plain,(
% 1.89/0.62    r2_hidden(sK3,k1_zfmisc_1(sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f95,f45])).
% 1.89/0.62  fof(f45,plain,(
% 1.89/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f15])).
% 1.89/0.62  fof(f15,axiom,(
% 1.89/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.89/0.62  fof(f95,plain,(
% 1.89/0.62    r2_hidden(sK3,k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 1.89/0.62    inference(resolution,[],[f51,f43])).
% 1.89/0.62  fof(f51,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f31])).
% 1.89/0.62  fof(f31,plain,(
% 1.89/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.89/0.62    inference(nnf_transformation,[],[f21])).
% 1.89/0.62  fof(f21,plain,(
% 1.89/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f12])).
% 1.89/0.62  fof(f12,axiom,(
% 1.89/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.89/0.62  fof(f64,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP0(X0,X1) | ~r2_hidden(X1,X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f41])).
% 1.89/0.62  fof(f41,plain,(
% 1.89/0.62    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(X1,sK6(X0,X1))) | ~sP0(X0,X1)))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(X1,sK6(X0,X1))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f39,plain,(
% 1.89/0.62    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) | ~sP0(X0,X1)))),
% 1.89/0.62    inference(rectify,[],[f38])).
% 1.89/0.62  fof(f38,plain,(
% 1.89/0.62    ! [X0,X2] : ((sP0(X0,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~sP0(X0,X2)))),
% 1.89/0.62    inference(nnf_transformation,[],[f26])).
% 1.89/0.62  fof(f26,plain,(
% 1.89/0.62    ! [X0,X2] : (sP0(X0,X2) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)))),
% 1.89/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.89/0.62  fof(f110,plain,(
% 1.89/0.62    ( ! [X2,X3] : (~sP0(k1_zfmisc_1(X2),X3) | r2_hidden(X3,X2)) )),
% 1.89/0.62    inference(resolution,[],[f59,f82])).
% 1.89/0.62  fof(f82,plain,(
% 1.89/0.62    ( ! [X0] : (sP1(k1_zfmisc_1(X0),X0)) )),
% 1.89/0.62    inference(superposition,[],[f81,f47])).
% 1.89/0.62  fof(f47,plain,(
% 1.89/0.62    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.89/0.62    inference(cnf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,axiom,(
% 1.89/0.62    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.89/0.62  fof(f81,plain,(
% 1.89/0.62    ( ! [X0] : (sP1(X0,k3_tarski(X0))) )),
% 1.89/0.62    inference(equality_resolution,[],[f65])).
% 1.89/0.62  fof(f65,plain,(
% 1.89/0.62    ( ! [X0,X1] : (sP1(X0,X1) | k3_tarski(X0) != X1) )),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k3_tarski(X0) != X1))),
% 1.89/0.62    inference(nnf_transformation,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP1(X0,X1))),
% 1.89/0.62    inference(definition_folding,[],[f9,f27,f26])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X0,X2)))),
% 1.89/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.89/0.62  fof(f9,axiom,(
% 1.89/0.62    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~sP0(X0,X3) | r2_hidden(X3,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f37])).
% 1.89/0.62  fof(f37,plain,(
% 1.89/0.62    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(X0,sK5(X0,X1)) | ~r2_hidden(sK5(X0,X1),X1)) & (sP0(X0,sK5(X0,X1)) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    ! [X1,X0] : (? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1))) => ((~sP0(X0,sK5(X0,X1)) | ~r2_hidden(sK5(X0,X1),X1)) & (sP0(X0,sK5(X0,X1)) | r2_hidden(sK5(X0,X1),X1))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f35,plain,(
% 1.89/0.62    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.89/0.62    inference(rectify,[],[f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X0,X2)) & (sP0(X0,X2) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.89/0.62    inference(nnf_transformation,[],[f27])).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (24661)------------------------------
% 1.89/0.62  % (24661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (24661)Termination reason: Refutation
% 1.89/0.63  
% 1.89/0.63  % (24661)Memory used [KB]: 1791
% 1.89/0.63  % (24661)Time elapsed: 0.177 s
% 1.89/0.63  % (24661)------------------------------
% 1.89/0.63  % (24661)------------------------------
% 1.89/0.63  % (24649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.89/0.63  % (24621)Success in time 0.261 s
%------------------------------------------------------------------------------
