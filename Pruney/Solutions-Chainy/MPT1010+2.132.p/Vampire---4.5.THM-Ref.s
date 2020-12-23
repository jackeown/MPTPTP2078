%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:09 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 156 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 ( 467 expanded)
%              Number of equality atoms :  122 ( 211 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f85,f105,f133])).

fof(f133,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_2 ),
    inference(superposition,[],[f67,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_2
  <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f34,f49,f50,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f105,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f92,f29])).

fof(f29,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f92,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK3,sK1)
    | ~ spl6_3 ),
    inference(superposition,[],[f30,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( sK2 = k1_funct_1(sK4,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK2 = k1_funct_1(sK4,X0)
        | sK2 = k1_funct_1(sK4,X0)
        | sK2 = k1_funct_1(sK4,X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f82,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_3
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f30,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( ~ v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_1
  <=> v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f83,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f71,f81,f77,f73])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
      | ~ v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
      | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(resolution,[],[f70,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f28,f50])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,X2,X0)
      | r2_hidden(k1_funct_1(sK4,X1),X0) ) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.34/0.55  % (26693)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.56  % (26693)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % (26684)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.56  % (26686)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f134,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f83,f85,f105,f133])).
% 1.34/0.56  fof(f133,plain,(
% 1.34/0.56    ~spl6_2),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f132])).
% 1.34/0.56  fof(f132,plain,(
% 1.34/0.56    $false | ~spl6_2),
% 1.34/0.56    inference(trivial_inequality_removal,[],[f122])).
% 1.34/0.56  fof(f122,plain,(
% 1.34/0.56    k1_xboole_0 != k1_xboole_0 | ~spl6_2),
% 1.34/0.56    inference(superposition,[],[f67,f79])).
% 1.34/0.56  fof(f79,plain,(
% 1.34/0.56    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl6_2),
% 1.34/0.56    inference(avatar_component_clause,[],[f77])).
% 1.34/0.56  fof(f77,plain,(
% 1.34/0.56    spl6_2 <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.34/0.56  fof(f67,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.34/0.56    inference(superposition,[],[f53,f54])).
% 1.34/0.56  fof(f54,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.34/0.56    inference(definition_unfolding,[],[f34,f49,f50,f50])).
% 1.34/0.56  fof(f50,plain,(
% 1.34/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f31,f49])).
% 1.34/0.56  fof(f31,plain,(
% 1.34/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f3])).
% 1.34/0.56  fof(f3,axiom,(
% 1.34/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f33,f48])).
% 1.34/0.56  fof(f48,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f35,f36])).
% 1.34/0.56  fof(f36,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f6])).
% 1.34/0.56  fof(f6,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.56  fof(f35,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f5])).
% 1.34/0.56  fof(f5,axiom,(
% 1.34/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.56  fof(f33,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f4])).
% 1.34/0.56  fof(f4,axiom,(
% 1.34/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.56  fof(f34,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f2])).
% 1.34/0.56  fof(f2,axiom,(
% 1.34/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.34/0.56  fof(f53,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f32,f50])).
% 1.34/0.56  fof(f32,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f7])).
% 1.34/0.56  fof(f7,axiom,(
% 1.34/0.56    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.34/0.56  fof(f105,plain,(
% 1.34/0.56    ~spl6_3),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f101])).
% 1.34/0.56  fof(f101,plain,(
% 1.34/0.56    $false | ~spl6_3),
% 1.34/0.56    inference(resolution,[],[f92,f29])).
% 1.34/0.56  fof(f29,plain,(
% 1.34/0.56    r2_hidden(sK3,sK1)),
% 1.34/0.56    inference(cnf_transformation,[],[f19])).
% 1.34/0.56  fof(f19,plain,(
% 1.34/0.56    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).
% 1.34/0.56  fof(f18,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f12,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.34/0.56    inference(flattening,[],[f11])).
% 1.34/0.56  fof(f11,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.34/0.56    inference(ennf_transformation,[],[f10])).
% 1.34/0.56  fof(f10,negated_conjecture,(
% 1.34/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.34/0.56    inference(negated_conjecture,[],[f9])).
% 1.34/0.56  fof(f9,conjecture,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.34/0.56  fof(f92,plain,(
% 1.34/0.56    ~r2_hidden(sK3,sK1) | ~spl6_3),
% 1.34/0.56    inference(trivial_inequality_removal,[],[f89])).
% 1.34/0.56  fof(f89,plain,(
% 1.34/0.56    sK2 != sK2 | ~r2_hidden(sK3,sK1) | ~spl6_3),
% 1.34/0.56    inference(superposition,[],[f30,f87])).
% 1.34/0.56  fof(f87,plain,(
% 1.34/0.56    ( ! [X0] : (sK2 = k1_funct_1(sK4,X0) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.34/0.56    inference(duplicate_literal_removal,[],[f86])).
% 1.34/0.56  fof(f86,plain,(
% 1.34/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | sK2 = k1_funct_1(sK4,X0) | sK2 = k1_funct_1(sK4,X0) | sK2 = k1_funct_1(sK4,X0)) ) | ~spl6_3),
% 1.34/0.56    inference(resolution,[],[f82,f62])).
% 1.34/0.56  fof(f62,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_enumset1(X2,X2,X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 1.34/0.56    inference(resolution,[],[f38,f60])).
% 1.34/0.56  fof(f60,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.34/0.56    inference(equality_resolution,[],[f56])).
% 1.34/0.56  fof(f56,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.34/0.56    inference(definition_unfolding,[],[f46,f48])).
% 1.34/0.56  fof(f46,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.34/0.56    inference(cnf_transformation,[],[f25])).
% 1.34/0.56  fof(f25,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.34/0.56    inference(nnf_transformation,[],[f17])).
% 1.34/0.56  fof(f17,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.34/0.56    inference(definition_folding,[],[f15,f16])).
% 1.34/0.56  fof(f16,plain,(
% 1.34/0.56    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.34/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.56  fof(f15,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.34/0.56    inference(ennf_transformation,[],[f1])).
% 1.34/0.56  fof(f1,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.34/0.56  fof(f38,plain,(
% 1.34/0.56    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.34/0.56    inference(cnf_transformation,[],[f24])).
% 1.34/0.56  fof(f24,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.34/0.56  fof(f23,plain,(
% 1.34/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f22,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.34/0.56    inference(rectify,[],[f21])).
% 1.34/0.56  fof(f21,plain,(
% 1.34/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.34/0.56    inference(flattening,[],[f20])).
% 1.34/0.56  fof(f20,plain,(
% 1.34/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.34/0.56    inference(nnf_transformation,[],[f16])).
% 1.34/0.56  fof(f82,plain,(
% 1.34/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.34/0.56    inference(avatar_component_clause,[],[f81])).
% 1.34/0.56  fof(f81,plain,(
% 1.34/0.56    spl6_3 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.34/0.56  fof(f30,plain,(
% 1.34/0.56    sK2 != k1_funct_1(sK4,sK3)),
% 1.34/0.56    inference(cnf_transformation,[],[f19])).
% 1.34/0.56  fof(f85,plain,(
% 1.34/0.56    spl6_1),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f84])).
% 1.34/0.56  fof(f84,plain,(
% 1.34/0.56    $false | spl6_1),
% 1.34/0.56    inference(resolution,[],[f75,f52])).
% 1.34/0.56  fof(f52,plain,(
% 1.34/0.56    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.34/0.56    inference(definition_unfolding,[],[f27,f50])).
% 1.34/0.56  fof(f27,plain,(
% 1.34/0.56    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.34/0.56    inference(cnf_transformation,[],[f19])).
% 1.34/0.56  fof(f75,plain,(
% 1.34/0.56    ~v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl6_1),
% 1.34/0.56    inference(avatar_component_clause,[],[f73])).
% 1.34/0.56  fof(f73,plain,(
% 1.34/0.56    spl6_1 <=> v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.34/0.56  fof(f83,plain,(
% 1.34/0.56    ~spl6_1 | spl6_2 | spl6_3),
% 1.34/0.56    inference(avatar_split_clause,[],[f71,f81,f77,f73])).
% 1.34/0.56  fof(f71,plain,(
% 1.34/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) )),
% 1.34/0.56    inference(resolution,[],[f70,f51])).
% 1.34/0.56  fof(f51,plain,(
% 1.34/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.34/0.56    inference(definition_unfolding,[],[f28,f50])).
% 1.34/0.56  fof(f28,plain,(
% 1.34/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.34/0.56    inference(cnf_transformation,[],[f19])).
% 1.34/0.56  fof(f70,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,X2,X0) | r2_hidden(k1_funct_1(sK4,X1),X0)) )),
% 1.34/0.56    inference(resolution,[],[f37,f26])).
% 1.34/0.56  fof(f26,plain,(
% 1.34/0.56    v1_funct_1(sK4)),
% 1.34/0.56    inference(cnf_transformation,[],[f19])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f14])).
% 1.34/0.56  fof(f14,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.34/0.56    inference(flattening,[],[f13])).
% 1.34/0.56  fof(f13,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.34/0.56    inference(ennf_transformation,[],[f8])).
% 1.34/0.56  fof(f8,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.34/0.56  % SZS output end Proof for theBenchmark
% 1.34/0.56  % (26693)------------------------------
% 1.34/0.56  % (26693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (26693)Termination reason: Refutation
% 1.34/0.56  
% 1.34/0.56  % (26693)Memory used [KB]: 6268
% 1.34/0.56  % (26693)Time elapsed: 0.124 s
% 1.34/0.56  % (26693)------------------------------
% 1.34/0.56  % (26693)------------------------------
% 1.34/0.57  % (26680)Success in time 0.197 s
%------------------------------------------------------------------------------
