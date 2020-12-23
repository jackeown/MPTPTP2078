%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 149 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 ( 612 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f160,f178,f179,f227,f232])).

fof(f232,plain,
    ( ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f230,f88])).

fof(f88,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f230,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f172,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f172,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f227,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f225,f173])).

fof(f173,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f225,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f214,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(sK1,X2,X3),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k1_enumset1(sK1,X2,X3),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k1_enumset1(sK1,sK2,X3),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k1_enumset1(sK1,sK2,X3),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X3,sK0) )
   => ( ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( k1_xboole_0 != X0
                 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

fof(f214,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f207,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f194,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f194,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f146,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f146,plain,(
    ! [X4,X3] :
      ( r2_hidden(k1_tarski(X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,X3)
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f144,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f144,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = X3
      | ~ m1_subset_1(X4,X3)
      | r2_hidden(k1_tarski(X4),k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f179,plain,
    ( spl6_1
    | spl6_8 ),
    inference(avatar_split_clause,[],[f116,f175,f87])).

fof(f175,plain,
    ( spl6_8
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f116,plain,
    ( r2_hidden(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f49,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f163,f154,f175,f171])).

fof(f154,plain,
    ( spl6_6
  <=> r1_tarski(k2_tarski(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f163,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK2,sK0)
    | spl6_6 ),
    inference(resolution,[],[f72,f156])).

fof(f156,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f160,plain,
    ( spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl6_1
    | spl6_5 ),
    inference(subsumption_resolution,[],[f158,f118])).

fof(f118,plain,
    ( r2_hidden(sK1,sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f114,f89])).

fof(f89,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f114,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f158,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl6_5 ),
    inference(resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f152,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_5
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f157,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f147,f154,f150])).

fof(f147,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK0)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f69,f132])).

fof(f132,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)),sK0) ),
    inference(resolution,[],[f126,f73])).

fof(f73,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f46,plain,(
    ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f126,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f121,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f50,f65])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

% (426)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (417)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (413)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (441)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (414)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (425)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (418)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (427)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (415)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (442)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (423)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (440)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (441)Refutation not found, incomplete strategy% (441)------------------------------
% 0.20/0.52  % (441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (436)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (441)Memory used [KB]: 10746
% 0.20/0.52  % (441)Time elapsed: 0.112 s
% 0.20/0.52  % (441)------------------------------
% 0.20/0.52  % (441)------------------------------
% 0.20/0.52  % (433)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (419)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (435)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (432)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (427)Refutation not found, incomplete strategy% (427)------------------------------
% 0.20/0.53  % (427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (422)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (427)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (427)Memory used [KB]: 1791
% 0.20/0.53  % (427)Time elapsed: 0.077 s
% 0.20/0.53  % (427)------------------------------
% 0.20/0.53  % (427)------------------------------
% 0.20/0.53  % (428)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (424)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (416)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (419)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f157,f160,f178,f179,f227,f232])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ~spl6_1 | ~spl6_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    $false | (~spl6_1 | ~spl6_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f230,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    v1_xboole_0(sK0) | ~spl6_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl6_1 <=> v1_xboole_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ~v1_xboole_0(sK0) | ~spl6_7),
% 0.20/0.53    inference(resolution,[],[f172,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    r2_hidden(sK2,sK0) | ~spl6_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    spl6_7 <=> r2_hidden(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    spl6_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    $false | spl6_7),
% 0.20/0.53    inference(subsumption_resolution,[],[f225,f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK0) | spl6_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f171])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    r2_hidden(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f214,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    k1_xboole_0 != sK0),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ((~m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f28,f27,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (~m1_subset_1(k1_enumset1(sK1,X2,X3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X3,sK0)) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X2] : (? [X3] : (~m1_subset_1(k1_enumset1(sK1,X2,X3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X3,sK0)) & m1_subset_1(X2,sK0)) => (? [X3] : (~m1_subset_1(k1_enumset1(sK1,sK2,X3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ? [X3] : (~m1_subset_1(k1_enumset1(sK1,sK2,X3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X3,sK0)) => (~m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK3,sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f15])).
% 0.20/0.53  fof(f15,conjecture,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | r2_hidden(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f207,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    m1_subset_1(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(resolution,[],[f194,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f146,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.53    inference(rectify,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X4,X3] : (r2_hidden(k1_tarski(X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,X3) | k1_xboole_0 = X3) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f144,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X4,X3) | r2_hidden(k1_tarski(X4),k1_zfmisc_1(X3)) | v1_xboole_0(k1_zfmisc_1(X3))) )),
% 0.20/0.53    inference(resolution,[],[f53,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    spl6_1 | spl6_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f116,f175,f87])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    spl6_8 <=> r2_hidden(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    r2_hidden(sK3,sK0) | v1_xboole_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f49,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    m1_subset_1(sK3,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ~spl6_7 | ~spl6_8 | spl6_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f163,f154,f175,f171])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    spl6_6 <=> r1_tarski(k2_tarski(sK2,sK3),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ~r2_hidden(sK3,sK0) | ~r2_hidden(sK2,sK0) | spl6_6),
% 0.20/0.53    inference(resolution,[],[f72,f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK2,sK3),sK0) | spl6_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(flattening,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    spl6_1 | spl6_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    $false | (spl6_1 | spl6_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f158,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | spl6_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f114,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~v1_xboole_0(sK0) | spl6_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f49,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    m1_subset_1(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK0) | spl6_5),
% 0.20/0.53    inference(resolution,[],[f152,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ~r1_tarski(k1_tarski(sK1),sK0) | spl6_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f150])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    spl6_5 <=> r1_tarski(k1_tarski(sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ~spl6_5 | ~spl6_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f147,f154,f150])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK2,sK3),sK0) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.20/0.53    inference(resolution,[],[f69,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ~r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)),sK0)),
% 0.20/0.53    inference(resolution,[],[f126,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~m1_subset_1(k2_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)),k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ~m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ( ! [X2,X1] : (m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r1_tarski(X1,X2)) )),
% 0.20/0.53    inference(resolution,[],[f121,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f50,f65])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  % (426)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (419)------------------------------
% 0.20/0.53  % (419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (419)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (419)Memory used [KB]: 10746
% 0.20/0.53  % (419)Time elapsed: 0.093 s
% 0.20/0.53  % (419)------------------------------
% 0.20/0.53  % (419)------------------------------
% 1.33/0.54  % (430)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.54  % (412)Success in time 0.177 s
%------------------------------------------------------------------------------
