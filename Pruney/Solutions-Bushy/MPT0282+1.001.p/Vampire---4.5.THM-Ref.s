%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0282+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 154 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  251 ( 723 expanded)
%              Number of equality atoms :   35 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f139,f429,f479,f495,f535,f629])).

fof(f629,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f99,f454,f498,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f498,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

% (22789)Refutation not found, incomplete strategy% (22789)------------------------------
% (22789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f18,plain,(
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

% (22789)Termination reason: Refutation not found, incomplete strategy

% (22789)Memory used [KB]: 1535
% (22789)Time elapsed: 0.093 s
% (22789)------------------------------
% (22789)------------------------------
fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f80,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_1
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f454,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f96,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_3
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f99,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f85,f41])).

fof(f85,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_2
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f535,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f25,f114])).

fof(f114,plain,
    ( k1_zfmisc_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_4
  <=> k1_zfmisc_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f25,plain,(
    k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
   => k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(f495,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f482,f83,f112,f94,f79])).

fof(f482,plain,
    ( k1_zfmisc_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f479,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f33,f155,f440,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f440,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK0)
    | spl4_2 ),
    inference(resolution,[],[f84,f40])).

fof(f84,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f155,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f429,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f81,f393,f41])).

fof(f393,plain,
    ( ! [X6] : ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(X6,sK1))
    | spl4_3 ),
    inference(superposition,[],[f370,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f370,plain,
    ( ! [X3] : ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,X3))
    | spl4_3 ),
    inference(resolution,[],[f174,f33])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),X0) )
    | spl4_3 ),
    inference(resolution,[],[f127,f32])).

fof(f127,plain,
    ( ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),sK1)
    | spl4_3 ),
    inference(resolution,[],[f95,f40])).

fof(f95,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f139,plain,
    ( spl4_1
    | spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f126,f94,f112,f79])).

fof(f126,plain,
    ( k1_zfmisc_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | spl4_3 ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f77,f83,f79])).

fof(f77,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),k1_zfmisc_1(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_zfmisc_1(k3_xboole_0(sK0,sK1)) != X0
      | r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X0),k1_zfmisc_1(sK0))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1),X0),X0) ) ),
    inference(superposition,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
