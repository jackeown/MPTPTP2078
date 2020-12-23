%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:55 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 ( 493 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(subsumption_resolution,[],[f242,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK5
    & r1_tarski(sK5,k3_subset_1(sK4,sK6))
    & r1_tarski(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK5
      & r1_tarski(sK5,k3_subset_1(sK4,sK6))
      & r1_tarski(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f242,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f241,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f241,plain,(
    ! [X0] : ~ r2_hidden(X0,sK5) ),
    inference(subsumption_resolution,[],[f238,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK6)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f96,f41])).

fof(f41,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f36])).

% (20971)Refutation not found, incomplete strategy% (20971)------------------------------
% (20971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f36,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

% (20971)Termination reason: Refutation not found, incomplete strategy

% (20971)Memory used [KB]: 10618
% (20971)Time elapsed: 0.126 s
% (20971)------------------------------
% (20971)------------------------------
fof(f17,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( sP2(X5,X3,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f57,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : sP3(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f18,f17])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP2(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP2(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f238,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f228,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f228,plain,(
    ! [X0] :
      ( sP0(sK6,X0,sK4)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f208,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X0,X1] : sP1(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f15,f14])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP0(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP0(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)))
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f193,f96])).

fof(f193,plain,(
    r1_tarski(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))) ),
    inference(resolution,[],[f192,f69])).

fof(f192,plain,(
    ! [X2] :
      ( ~ sP1(sK4,sK6,X2)
      | r1_tarski(sK5,X2) ) ),
    inference(subsumption_resolution,[],[f187,f40])).

fof(f40,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f187,plain,(
    ! [X2] :
      ( r1_tarski(sK5,X2)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK4))
      | ~ sP1(sK4,sK6,X2) ) ),
    inference(superposition,[],[f42,f125])).

fof(f125,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = X4
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ sP1(X2,X3,X4) ) ),
    inference(superposition,[],[f66,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f56,f45])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,(
    r1_tarski(sK5,k3_subset_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (20972)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (20972)Refutation not found, incomplete strategy% (20972)------------------------------
% 0.21/0.49  % (20972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20972)Memory used [KB]: 10618
% 0.21/0.49  % (20972)Time elapsed: 0.102 s
% 0.21/0.49  % (20972)------------------------------
% 0.21/0.49  % (20972)------------------------------
% 0.21/0.50  % (20965)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20988)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (20980)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.53  % (20981)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.53  % (20983)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (20971)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.54  % (20983)Refutation not found, incomplete strategy% (20983)------------------------------
% 1.32/0.54  % (20983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (20983)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (20983)Memory used [KB]: 10618
% 1.32/0.54  % (20983)Time elapsed: 0.070 s
% 1.32/0.54  % (20983)------------------------------
% 1.32/0.54  % (20983)------------------------------
% 1.32/0.54  % (20967)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (20966)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (20969)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.55  % (20989)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.55  % (20975)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.55  % (20973)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (20970)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.56  % (20964)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.56  % (20988)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f246,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(subsumption_resolution,[],[f242,f43])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    k1_xboole_0 != sK5),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    k1_xboole_0 != sK5 & r1_tarski(sK5,k3_subset_1(sK4,sK6)) & r1_tarski(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK4))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK5 & r1_tarski(sK5,k3_subset_1(sK4,sK6)) & r1_tarski(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK4)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f10,plain,(
% 1.49/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(flattening,[],[f9])).
% 1.49/0.56  fof(f9,plain,(
% 1.49/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.49/0.56    inference(negated_conjecture,[],[f7])).
% 1.49/0.56  fof(f7,conjecture,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.49/0.56  fof(f242,plain,(
% 1.49/0.56    k1_xboole_0 = sK5),
% 1.49/0.56    inference(resolution,[],[f241,f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f11,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.49/0.56  fof(f241,plain,(
% 1.49/0.56    ( ! [X0] : (~r2_hidden(X0,sK5)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f238,f98])).
% 1.49/0.56  fof(f98,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(X0,sK6) | ~r2_hidden(X0,sK5)) )),
% 1.49/0.56    inference(resolution,[],[f96,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    r1_tarski(sK5,sK6)),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f96,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.49/0.56    inference(resolution,[],[f92,f62])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 1.49/0.56    inference(rectify,[],[f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 1.49/0.56    inference(flattening,[],[f36])).
% 1.49/0.56  % (20971)Refutation not found, incomplete strategy% (20971)------------------------------
% 1.49/0.56  % (20971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f17])).
% 1.49/0.56  % (20971)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (20971)Memory used [KB]: 10618
% 1.49/0.56  % (20971)Time elapsed: 0.126 s
% 1.49/0.56  % (20971)------------------------------
% 1.49/0.56  % (20971)------------------------------
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.56  fof(f92,plain,(
% 1.49/0.56    ( ! [X4,X5,X3] : (sP2(X5,X3,X4) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,X5)) )),
% 1.49/0.56    inference(resolution,[],[f57,f71])).
% 1.49/0.56  fof(f71,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP3(X0,X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(superposition,[],[f70,f46])).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,plain,(
% 1.49/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP3(X0,X1,k3_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(equality_resolution,[],[f64])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.49/0.56    inference(cnf_transformation,[],[f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.49/0.56    inference(nnf_transformation,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 1.49/0.56    inference(definition_folding,[],[f1,f18,f17])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP2(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f33,f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP2(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.49/0.56    inference(rectify,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 1.49/0.56    inference(nnf_transformation,[],[f18])).
% 1.49/0.56  fof(f238,plain,(
% 1.49/0.56    ( ! [X0] : (~r2_hidden(X0,sK5) | ~r2_hidden(X0,sK6)) )),
% 1.49/0.56    inference(resolution,[],[f228,f53])).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.49/0.56    inference(rectify,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.49/0.56    inference(flattening,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f14])).
% 1.49/0.56  fof(f14,plain,(
% 1.49/0.56    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.56  fof(f228,plain,(
% 1.49/0.56    ( ! [X0] : (sP0(sK6,X0,sK4) | ~r2_hidden(X0,sK5)) )),
% 1.49/0.56    inference(resolution,[],[f208,f85])).
% 1.49/0.56  fof(f85,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | sP0(X2,X0,X1)) )),
% 1.49/0.56    inference(resolution,[],[f48,f69])).
% 1.49/0.56  fof(f69,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP1(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.49/0.56    inference(equality_resolution,[],[f68])).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.49/0.56    inference(definition_unfolding,[],[f55,f45])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.49/0.56    inference(nnf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.49/0.56    inference(definition_folding,[],[f2,f15,f14])).
% 1.49/0.56  fof(f15,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.49/0.56  fof(f48,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.49/0.56    inference(rectify,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.49/0.56    inference(nnf_transformation,[],[f15])).
% 1.49/0.56  fof(f208,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))) | ~r2_hidden(X0,sK5)) )),
% 1.49/0.56    inference(resolution,[],[f193,f96])).
% 1.49/0.56  fof(f193,plain,(
% 1.49/0.56    r1_tarski(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)))),
% 1.49/0.56    inference(resolution,[],[f192,f69])).
% 1.49/0.56  fof(f192,plain,(
% 1.49/0.56    ( ! [X2] : (~sP1(sK4,sK6,X2) | r1_tarski(sK5,X2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f187,f40])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    m1_subset_1(sK6,k1_zfmisc_1(sK4))),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f187,plain,(
% 1.49/0.56    ( ! [X2] : (r1_tarski(sK5,X2) | ~m1_subset_1(sK6,k1_zfmisc_1(sK4)) | ~sP1(sK4,sK6,X2)) )),
% 1.49/0.56    inference(superposition,[],[f42,f125])).
% 1.49/0.56  fof(f125,plain,(
% 1.49/0.56    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = X4 | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~sP1(X2,X3,X4)) )),
% 1.49/0.56    inference(superposition,[],[f66,f67])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~sP1(X0,X1,X2)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f56,f45])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f47,f45])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,plain,(
% 1.49/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    r1_tarski(sK5,k3_subset_1(sK4,sK6))),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (20988)------------------------------
% 1.49/0.56  % (20988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (20988)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (20988)Memory used [KB]: 6268
% 1.49/0.56  % (20988)Time elapsed: 0.152 s
% 1.49/0.56  % (20988)------------------------------
% 1.49/0.56  % (20988)------------------------------
% 1.49/0.56  % (20960)Success in time 0.198 s
%------------------------------------------------------------------------------
