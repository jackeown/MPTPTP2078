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
% DateTime   : Thu Dec  3 12:44:35 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 345 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  364 (1433 expanded)
%              Number of equality atoms :   80 ( 327 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f122,f607,f1212])).

fof(f1212,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1211])).

fof(f1211,plain,
    ( $false
    | spl6_14 ),
    inference(subsumption_resolution,[],[f1208,f501])).

fof(f501,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl6_14
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1208,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f1195,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1195,plain,(
    ! [X1] : ~ r2_hidden(X1,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f1191,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f91,f132])).

fof(f132,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f129,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f128,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f128,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f126,f47])).

% (27069)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f126,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
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

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

% (27068)Refutation not found, incomplete strategy% (27068)------------------------------
% (27068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27068)Termination reason: Refutation not found, incomplete strategy

% (27068)Memory used [KB]: 10746
% (27068)Time elapsed: 0.149 s
% (27068)------------------------------
% (27068)------------------------------
fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1191,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k5_xboole_0(sK1,sK1)) ) ),
    inference(superposition,[],[f90,f143])).

fof(f143,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f76,f132])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f53,f54,f54])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f71,f54])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f607,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f591,f552])).

fof(f552,plain,
    ( r2_hidden(sK2(sK1),k1_xboole_0)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f549,f100])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f549,plain,
    ( r2_hidden(sK2(sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f517,f51])).

fof(f517,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f209,f502])).

fof(f502,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f500])).

fof(f209,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k5_xboole_0(sK1,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f148,f159])).

fof(f159,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f90,f125])).

fof(f125,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f44,f80])).

% (27080)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f54])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

% (27074)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

% (27075)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f148,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k5_xboole_0(sK1,sK1))
        | r2_hidden(X2,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_3 ),
    inference(superposition,[],[f89,f134])).

fof(f134,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f105,f62])).

fof(f105,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f72,f54])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f591,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f590,f508])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK1) )
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f138,f502])).

fof(f590,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f583,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f583,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_14 ),
    inference(superposition,[],[f90,f514])).

fof(f514,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f145,f502])).

fof(f145,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f142,f62])).

fof(f142,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f79,f132])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f122,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f120,f116])).

fof(f116,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f115,f88])).

fof(f115,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f110,f47])).

fof(f110,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f108,f55])).

fof(f108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f44,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f120,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f96,f113])).

fof(f113,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f112,f50])).

fof(f112,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f109,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f109,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_2 ),
    inference(resolution,[],[f108,f80])).

fof(f96,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f106,plain,
    ( spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f78,f98,f103])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f92,f98,f94])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27065)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (27081)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (27073)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (27057)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (27058)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (27060)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27061)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27062)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (27084)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (27070)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (27064)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (27068)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27078)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (27085)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (27083)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27082)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27059)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27077)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (27065)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % (27086)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (27079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (27071)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f1213,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f101,f106,f122,f607,f1212])).
% 1.41/0.55  fof(f1212,plain,(
% 1.41/0.55    spl6_14),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f1211])).
% 1.41/0.55  fof(f1211,plain,(
% 1.41/0.55    $false | spl6_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f1208,f501])).
% 1.41/0.55  fof(f501,plain,(
% 1.41/0.55    k1_xboole_0 != k5_xboole_0(sK1,sK1) | spl6_14),
% 1.41/0.55    inference(avatar_component_clause,[],[f500])).
% 1.41/0.55  fof(f500,plain,(
% 1.41/0.55    spl6_14 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.41/0.55  fof(f1208,plain,(
% 1.41/0.55    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.41/0.55    inference(resolution,[],[f1195,f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.41/0.55  fof(f1195,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK1,sK1))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f1191,f138])).
% 1.41/0.55  fof(f138,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 1.41/0.55    inference(superposition,[],[f91,f132])).
% 1.41/0.55  fof(f132,plain,(
% 1.41/0.55    sK1 = k3_xboole_0(sK1,sK0)),
% 1.41/0.55    inference(resolution,[],[f129,f62])).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    r1_tarski(sK1,sK0)),
% 1.41/0.55    inference(resolution,[],[f128,f88])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f66])).
% 1.41/0.55  fof(f66,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f38])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.41/0.55    inference(rectify,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.55    inference(subsumption_resolution,[],[f126,f47])).
% 1.41/0.55  % (27069)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,axiom,(
% 1.41/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.41/0.55  fof(f126,plain,(
% 1.41/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.41/0.55    inference(resolution,[],[f44,f55])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(nnf_transformation,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(flattening,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(nnf_transformation,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f17])).
% 1.41/0.55  fof(f17,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.41/0.55    inference(negated_conjecture,[],[f16])).
% 1.41/0.55  fof(f16,conjecture,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f86])).
% 1.41/0.55  fof(f86,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.41/0.55    inference(definition_unfolding,[],[f70,f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.55  fof(f70,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.41/0.55  % (27068)Refutation not found, incomplete strategy% (27068)------------------------------
% 1.41/0.55  % (27068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (27068)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (27068)Memory used [KB]: 10746
% 1.41/0.55  % (27068)Time elapsed: 0.149 s
% 1.41/0.55  % (27068)------------------------------
% 1.41/0.55  % (27068)------------------------------
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(rectify,[],[f40])).
% 1.41/0.55  fof(f40,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(flattening,[],[f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(nnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.55  fof(f1191,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k5_xboole_0(sK1,sK1))) )),
% 1.41/0.55    inference(superposition,[],[f90,f143])).
% 1.41/0.55  fof(f143,plain,(
% 1.41/0.55    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))),
% 1.41/0.55    inference(superposition,[],[f76,f132])).
% 1.41/0.55  fof(f76,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.41/0.55    inference(definition_unfolding,[],[f53,f54,f54])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.55  fof(f90,plain,(
% 1.41/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f85])).
% 1.41/0.55  fof(f85,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.41/0.55    inference(definition_unfolding,[],[f71,f54])).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f607,plain,(
% 1.41/0.55    spl6_2 | ~spl6_3 | ~spl6_14),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f603])).
% 1.41/0.55  fof(f603,plain,(
% 1.41/0.55    $false | (spl6_2 | ~spl6_3 | ~spl6_14)),
% 1.41/0.55    inference(resolution,[],[f591,f552])).
% 1.41/0.55  fof(f552,plain,(
% 1.41/0.55    r2_hidden(sK2(sK1),k1_xboole_0) | (spl6_2 | ~spl6_3 | ~spl6_14)),
% 1.41/0.55    inference(subsumption_resolution,[],[f549,f100])).
% 1.41/0.55  fof(f100,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | spl6_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f98])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    spl6_2 <=> k1_xboole_0 = sK1),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.55  fof(f549,plain,(
% 1.41/0.55    r2_hidden(sK2(sK1),k1_xboole_0) | k1_xboole_0 = sK1 | (~spl6_3 | ~spl6_14)),
% 1.41/0.55    inference(resolution,[],[f517,f51])).
% 1.41/0.55  fof(f517,plain,(
% 1.41/0.55    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,k1_xboole_0)) ) | (~spl6_3 | ~spl6_14)),
% 1.41/0.55    inference(backward_demodulation,[],[f209,f502])).
% 1.41/0.55  fof(f502,plain,(
% 1.41/0.55    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl6_14),
% 1.41/0.55    inference(avatar_component_clause,[],[f500])).
% 1.41/0.55  fof(f209,plain,(
% 1.41/0.55    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X2,sK1)) ) | ~spl6_3),
% 1.41/0.55    inference(subsumption_resolution,[],[f148,f159])).
% 1.41/0.55  fof(f159,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 1.41/0.55    inference(superposition,[],[f90,f125])).
% 1.41/0.55  fof(f125,plain,(
% 1.41/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.41/0.55    inference(resolution,[],[f44,f80])).
% 1.41/0.55  % (27080)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  fof(f80,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f63,f54])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  % (27074)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  % (27075)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  fof(f14,axiom,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.41/0.55  fof(f148,plain,(
% 1.41/0.55    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(sK1,sK1)) | r2_hidden(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | ~spl6_3),
% 1.41/0.55    inference(superposition,[],[f89,f134])).
% 1.41/0.55  fof(f134,plain,(
% 1.41/0.55    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl6_3),
% 1.41/0.55    inference(resolution,[],[f105,f62])).
% 1.41/0.55  fof(f105,plain,(
% 1.41/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl6_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f103])).
% 1.41/0.55  fof(f103,plain,(
% 1.41/0.55    spl6_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f84])).
% 1.41/0.55  fof(f84,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.41/0.55    inference(definition_unfolding,[],[f72,f54])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f591,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f590,f508])).
% 1.41/0.55  fof(f508,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK1)) ) | ~spl6_14),
% 1.41/0.55    inference(backward_demodulation,[],[f138,f502])).
% 1.41/0.55  fof(f590,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK1)) ) | ~spl6_14),
% 1.41/0.55    inference(forward_demodulation,[],[f583,f50])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.41/0.55  fof(f583,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X1,sK1)) ) | ~spl6_14),
% 1.41/0.55    inference(superposition,[],[f90,f514])).
% 1.41/0.55  fof(f514,plain,(
% 1.41/0.55    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl6_14),
% 1.41/0.55    inference(backward_demodulation,[],[f145,f502])).
% 1.41/0.55  fof(f145,plain,(
% 1.41/0.55    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 1.41/0.55    inference(resolution,[],[f142,f62])).
% 1.41/0.55  fof(f142,plain,(
% 1.41/0.55    r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 1.41/0.55    inference(superposition,[],[f79,f132])).
% 1.41/0.55  fof(f79,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f52,f54])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.41/0.55  fof(f122,plain,(
% 1.41/0.55    spl6_1 | ~spl6_2),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f121])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    $false | (spl6_1 | ~spl6_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f120,f116])).
% 1.41/0.55  fof(f116,plain,(
% 1.41/0.55    r1_tarski(k1_xboole_0,sK0) | ~spl6_2),
% 1.41/0.55    inference(resolution,[],[f115,f88])).
% 1.41/0.55  fof(f115,plain,(
% 1.41/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.41/0.55    inference(subsumption_resolution,[],[f110,f47])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.41/0.55    inference(resolution,[],[f108,f55])).
% 1.41/0.55  fof(f108,plain,(
% 1.41/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.41/0.55    inference(backward_demodulation,[],[f44,f99])).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | ~spl6_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f98])).
% 1.41/0.55  fof(f120,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,sK0) | (spl6_1 | ~spl6_2)),
% 1.41/0.55    inference(forward_demodulation,[],[f96,f113])).
% 1.41/0.55  fof(f113,plain,(
% 1.41/0.55    sK0 = k3_subset_1(sK0,k1_xboole_0) | ~spl6_2),
% 1.41/0.55    inference(forward_demodulation,[],[f112,f50])).
% 1.41/0.55  fof(f112,plain,(
% 1.41/0.55    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 1.41/0.55    inference(forward_demodulation,[],[f109,f49])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.41/0.55  fof(f109,plain,(
% 1.41/0.55    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) | ~spl6_2),
% 1.41/0.55    inference(resolution,[],[f108,f80])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl6_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f94])).
% 1.41/0.55  fof(f94,plain,(
% 1.41/0.55    spl6_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    spl6_3 | spl6_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f78,f98,f103])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.41/0.55    inference(definition_unfolding,[],[f45,f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,axiom,(
% 1.41/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f101,plain,(
% 1.41/0.55    ~spl6_1 | ~spl6_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f92,f98,f94])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.41/0.55    inference(inner_rewriting,[],[f77])).
% 1.41/0.55  fof(f77,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.41/0.55    inference(definition_unfolding,[],[f46,f48])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (27065)------------------------------
% 1.41/0.55  % (27065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (27065)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (27065)Memory used [KB]: 11129
% 1.41/0.55  % (27065)Time elapsed: 0.125 s
% 1.41/0.55  % (27065)------------------------------
% 1.41/0.55  % (27065)------------------------------
% 1.41/0.55  % (27063)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (27056)Success in time 0.188 s
%------------------------------------------------------------------------------
