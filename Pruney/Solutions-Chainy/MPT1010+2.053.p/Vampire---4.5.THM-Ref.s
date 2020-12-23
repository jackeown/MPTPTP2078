%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 214 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  404 ( 767 expanded)
%              Number of equality atoms :  122 ( 237 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f229,f319,f335,f467])).

fof(f467,plain,(
    ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl12_11 ),
    inference(resolution,[],[f368,f110])).

fof(f110,plain,(
    ! [X2,X3,X1] : sP5(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP5(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP5(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP5(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP5(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP5(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP5(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X1,X0] :
      ( sP5(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f368,plain,
    ( ! [X0] : ~ sP5(X0,sK8,sK8,sK8)
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f356,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f356,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ sP5(X0,sK8,sK8,sK8) )
    | ~ spl12_11 ),
    inference(superposition,[],[f149,f339])).

fof(f339,plain,
    ( k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8)
    | ~ spl12_11 ),
    inference(resolution,[],[f318,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f318,plain,
    ( sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl12_11
  <=> sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(k2_enumset1(X7,X7,X6,X5),X4)
      | ~ sP5(X4,X5,X6,X7) ) ),
    inference(resolution,[],[f145,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_enumset1(X3,X3,X2,X1))
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f85,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : sP6(X0,X1,X2,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X0,X1,X2,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f92,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP6(X0,X1,X2,X3) )
      & ( sP6(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP6(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f25,f34,f33])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( sP6(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP5(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | ~ sP5(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP6(X0,X1,X2,X3)
        | ( ( ~ sP5(sK11(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
          & ( sP5(sK11(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP5(X5,X2,X1,X0) )
            & ( sP5(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP6(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP5(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP5(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP5(sK11(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
        & ( sP5(sK11(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP6(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP5(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP5(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP5(X5,X2,X1,X0) )
            & ( sP5(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP6(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP6(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP5(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP5(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP5(X4,X2,X1,X0) )
            & ( sP5(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP6(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f335,plain,
    ( spl12_2
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl12_2
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f60,plain,(
    r2_hidden(sK9,sK7) ),
    inference(cnf_transformation,[],[f37])).

% (9342)Refutation not found, incomplete strategy% (9342)------------------------------
% (9342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9342)Termination reason: Refutation not found, incomplete strategy

% (9342)Memory used [KB]: 10746
% (9342)Time elapsed: 0.126 s
% (9342)------------------------------
% (9342)------------------------------
fof(f37,plain,
    ( sK8 != k1_funct_1(sK10,sK9)
    & r2_hidden(sK9,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_2(sK10,sK7,k1_tarski(sK8))
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f16,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK8 != k1_funct_1(sK10,sK9)
      & r2_hidden(sK9,sK7)
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
      & v1_funct_2(sK10,sK7,k1_tarski(sK8))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f325,plain,
    ( ~ r2_hidden(sK9,sK7)
    | spl12_2
    | ~ spl12_10 ),
    inference(backward_demodulation,[],[f162,f314])).

fof(f314,plain,
    ( sK7 = k1_relat_1(sK10)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl12_10
  <=> sK7 = k1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f162,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK10))
    | spl12_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl12_2
  <=> r2_hidden(sK9,k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f319,plain,
    ( spl12_10
    | spl12_11 ),
    inference(avatar_split_clause,[],[f310,f316,f312])).

fof(f310,plain,
    ( sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8))
    | sK7 = k1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f308,f100])).

fof(f100,plain,(
    v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(definition_unfolding,[],[f58,f98])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f37])).

fof(f308,plain,
    ( ~ v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8))
    | sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8))
    | sK7 = k1_relat_1(sK10) ),
    inference(resolution,[],[f186,f99])).

fof(f99,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) ),
    inference(definition_unfolding,[],[f59,f98])).

fof(f59,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f186,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f184,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f24,f31,f30,f29])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | ~ sP3(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f78,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f229,plain,(
    ~ spl12_2 ),
    inference(avatar_split_clause,[],[f228,f161])).

fof(f228,plain,(
    ~ r2_hidden(sK9,k1_relat_1(sK10)) ),
    inference(trivial_inequality_removal,[],[f219])).

fof(f219,plain,
    ( sK8 != sK8
    | ~ r2_hidden(sK9,k1_relat_1(sK10)) ),
    inference(superposition,[],[f61,f216])).

fof(f216,plain,(
    ! [X0] :
      ( sK8 = k1_funct_1(sK10,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f215,f115])).

fof(f115,plain,(
    v1_relat_1(sK10) ),
    inference(resolution,[],[f74,f99])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f215,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK10))
      | sK8 = k1_funct_1(sK10,X0)
      | ~ v1_relat_1(sK10) ) ),
    inference(subsumption_resolution,[],[f212,f57])).

fof(f57,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f37])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK10))
      | sK8 = k1_funct_1(sK10,X0)
      | ~ v1_funct_1(sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(resolution,[],[f194,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          & sP0(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f27,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f194,plain,(
    ! [X6] :
      ( ~ sP0(sK10,k1_funct_1(sK10,X6),X6)
      | ~ r2_hidden(X6,k1_relat_1(sK10))
      | sK8 = k1_funct_1(sK10,X6) ) ),
    inference(resolution,[],[f105,f173])).

fof(f173,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X9),sK10)
      | sK8 = X9 ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X10,X9] :
      ( sK8 = X9
      | sK8 = X9
      | sK8 = X9
      | ~ r2_hidden(k4_tarski(X10,X9),sK10) ) ),
    inference(resolution,[],[f88,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK8,sK8,sK8)
      | ~ r2_hidden(k4_tarski(X1,X0),sK10) ) ),
    inference(resolution,[],[f144,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8))
      | ~ r2_hidden(k4_tarski(X1,X0),sK10) ) ),
    inference(resolution,[],[f95,f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))
      | ~ r2_hidden(X0,sK10) ) ),
    inference(resolution,[],[f71,f99])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
      | sP5(X0,X3,X2,X1) ) ),
    inference(resolution,[],[f84,f113])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP5(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f105,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,k1_funct_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f66])).

% (9355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) != X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X0,X2) = X1
          | ~ r2_hidden(k4_tarski(X2,X1),X0) )
        & ( r2_hidden(k4_tarski(X2,X1),X0)
          | k1_funct_1(X0,X2) != X1 ) )
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        & ( r2_hidden(k4_tarski(X1,X2),X0)
          | k1_funct_1(X0,X1) != X2 ) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    sK8 != k1_funct_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:48:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (9334)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (9360)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (9332)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9342)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (9360)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (9343)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9335)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (9340)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (9362)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (9331)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9330)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (9354)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9333)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (9352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (9341)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (9361)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (9345)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f468,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f229,f319,f335,f467])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    ~spl12_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f461])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    $false | ~spl12_11),
% 0.21/0.54    inference(resolution,[],[f368,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (sP5(X1,X1,X2,X3)) )),
% 0.21/0.54    inference(equality_resolution,[],[f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP5(X0,X1,X2,X3) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP5(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP5(X0,X1,X2,X3)))),
% 0.21/0.54    inference(rectify,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X4,X2,X1,X0] : ((sP5(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP5(X4,X2,X1,X0)))),
% 0.21/0.54    inference(flattening,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X4,X2,X1,X0] : ((sP5(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP5(X4,X2,X1,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X4,X2,X1,X0] : (sP5(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    ( ! [X0] : (~sP5(X0,sK8,sK8,sK8)) ) | ~spl12_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f356,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~sP5(X0,sK8,sK8,sK8)) ) | ~spl12_11),
% 0.21/0.54    inference(superposition,[],[f149,f339])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) | ~spl12_11),
% 0.21/0.54    inference(resolution,[],[f318,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8)) | ~spl12_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f316])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    spl12_11 <=> sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (~r1_tarski(k2_enumset1(X7,X7,X6,X5),X4) | ~sP5(X4,X5,X6,X7)) )),
% 0.21/0.54    inference(resolution,[],[f145,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X3,X3,X2,X1)) | ~sP5(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f85,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP6(X0,X1,X2,k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP6(X0,X1,X2,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.54    inference(definition_unfolding,[],[f92,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP6(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP6(X0,X1,X2,X3)) & (sP6(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP6(X0,X1,X2,X3))),
% 0.21/0.54    inference(definition_folding,[],[f25,f34,f33])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (sP6(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP5(X4,X2,X1,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP6(X0,X1,X2,X3) | ~sP5(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP6(X0,X1,X2,X3) | ((~sP5(sK11(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK11(X0,X1,X2,X3),X3)) & (sP5(sK11(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK11(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP5(X5,X2,X1,X0)) & (sP5(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP6(X0,X1,X2,X3)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X4] : ((~sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP5(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP5(sK11(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK11(X0,X1,X2,X3),X3)) & (sP5(sK11(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK11(X0,X1,X2,X3),X3))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP6(X0,X1,X2,X3) | ? [X4] : ((~sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP5(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP5(X5,X2,X1,X0)) & (sP5(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP6(X0,X1,X2,X3)))),
% 0.21/0.54    inference(rectify,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP6(X0,X1,X2,X3) | ? [X4] : ((~sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP5(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP5(X4,X2,X1,X0)) & (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP6(X0,X1,X2,X3)))),
% 0.21/0.54    inference(nnf_transformation,[],[f34])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    spl12_2 | ~spl12_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f334])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    $false | (spl12_2 | ~spl12_10)),
% 0.21/0.54    inference(subsumption_resolution,[],[f325,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    r2_hidden(sK9,sK7)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % (9342)Refutation not found, incomplete strategy% (9342)------------------------------
% 0.21/0.54  % (9342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9342)Memory used [KB]: 10746
% 0.21/0.54  % (9342)Time elapsed: 0.126 s
% 0.21/0.54  % (9342)------------------------------
% 0.21/0.54  % (9342)------------------------------
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    sK8 != k1_funct_1(sK10,sK9) & r2_hidden(sK9,sK7) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) & v1_funct_2(sK10,sK7,k1_tarski(sK8)) & v1_funct_1(sK10)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f16,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK8 != k1_funct_1(sK10,sK9) & r2_hidden(sK9,sK7) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) & v1_funct_2(sK10,sK7,k1_tarski(sK8)) & v1_funct_1(sK10))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    ~r2_hidden(sK9,sK7) | (spl12_2 | ~spl12_10)),
% 0.21/0.54    inference(backward_demodulation,[],[f162,f314])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    sK7 = k1_relat_1(sK10) | ~spl12_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f312])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    spl12_10 <=> sK7 = k1_relat_1(sK10)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ~r2_hidden(sK9,k1_relat_1(sK10)) | spl12_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    spl12_2 <=> r2_hidden(sK9,k1_relat_1(sK10))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    spl12_10 | spl12_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f310,f316,f312])).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8)) | sK7 = k1_relat_1(sK10)),
% 0.21/0.54    inference(subsumption_resolution,[],[f308,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8))),
% 0.21/0.54    inference(definition_unfolding,[],[f58,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f63,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    v1_funct_2(sK10,sK7,k1_tarski(sK8))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    ~v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8)) | sP2(sK7,k2_enumset1(sK8,sK8,sK8,sK8)) | sK7 = k1_relat_1(sK10)),
% 0.21/0.54    inference(resolution,[],[f186,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))),
% 0.21/0.54    inference(definition_unfolding,[],[f59,f98])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f184,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f24,f31,f30,f29])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | ~sP3(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.54    inference(superposition,[],[f78,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f30])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ~spl12_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f228,f161])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ~r2_hidden(sK9,k1_relat_1(sK10))),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f219])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    sK8 != sK8 | ~r2_hidden(sK9,k1_relat_1(sK10))),
% 0.21/0.54    inference(superposition,[],[f61,f216])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0] : (sK8 = k1_funct_1(sK10,X0) | ~r2_hidden(X0,k1_relat_1(sK10))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    v1_relat_1(sK10)),
% 0.21/0.54    inference(resolution,[],[f74,f99])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK10)) | sK8 = k1_funct_1(sK10,X0) | ~v1_relat_1(sK10)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f212,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_1(sK10)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK10)) | sK8 = k1_funct_1(sK10,X0) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) )),
% 0.21/0.54    inference(resolution,[],[f194,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (sP1(X2,X1,X0) & sP0(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(definition_folding,[],[f18,f27,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ( ! [X6] : (~sP0(sK10,k1_funct_1(sK10,X6),X6) | ~r2_hidden(X6,k1_relat_1(sK10)) | sK8 = k1_funct_1(sK10,X6)) )),
% 0.21/0.54    inference(resolution,[],[f105,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X10,X9),sK10) | sK8 = X9) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X10,X9] : (sK8 = X9 | sK8 = X9 | sK8 = X9 | ~r2_hidden(k4_tarski(X10,X9),sK10)) )),
% 0.21/0.54    inference(resolution,[],[f88,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP5(X0,sK8,sK8,sK8) | ~r2_hidden(k4_tarski(X1,X0),sK10)) )),
% 0.21/0.54    inference(resolution,[],[f144,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8)) | ~r2_hidden(k4_tarski(X1,X0),sK10)) )),
% 0.21/0.54    inference(resolution,[],[f95,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))) | ~r2_hidden(X0,sK10)) )),
% 0.21/0.54    inference(resolution,[],[f71,f99])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.54    inference(flattening,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.54    inference(nnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) | sP5(X0,X3,X2,X1)) )),
% 0.21/0.54    inference(resolution,[],[f84,f113])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP6(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP5(X5,X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~sP5(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,k1_funct_1(X0,X2),X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f66])).
% 0.21/0.54  % (9355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1 | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((k1_funct_1(X0,X2) = X1 | ~r2_hidden(k4_tarski(X2,X1),X0)) & (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    sK8 != k1_funct_1(sK10,sK9)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (9360)------------------------------
% 0.21/0.54  % (9360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9360)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (9360)Memory used [KB]: 6396
% 0.21/0.54  % (9360)Time elapsed: 0.115 s
% 0.21/0.54  % (9360)------------------------------
% 0.21/0.54  % (9360)------------------------------
% 0.21/0.54  % (9356)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (9357)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (9326)Success in time 0.181 s
%------------------------------------------------------------------------------
