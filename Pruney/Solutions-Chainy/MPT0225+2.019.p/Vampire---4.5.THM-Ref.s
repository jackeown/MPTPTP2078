%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 676 expanded)
%              Number of leaves         :   22 ( 200 expanded)
%              Depth                    :   19
%              Number of atoms          :  343 (2099 expanded)
%              Number of equality atoms :   86 ( 435 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f578,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f79,f429,f472,f491,f500,f524,f577])).

fof(f577,plain,
    ( spl4_5
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f570,f96])).

fof(f96,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f570,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f565,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f565,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f558,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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

fof(f558,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_zfmisc_1(X0))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f529,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ r1_tarski(X0,X2)
      | r2_hidden(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f529,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f413,f128])).

fof(f128,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k3_enumset1(X8,X8,X8,X8,X8))
      | r2_hidden(X8,k3_enumset1(X9,X9,X9,X9,X9)) ) ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f112,f57])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK2(X4,X5),X3)
      | ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f413,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl4_9
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f524,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f512,f183])).

fof(f183,plain,(
    ! [X0] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f177,f61])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f115,f60])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f113,f57])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f84,f36])).

fof(f512,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f475,f194])).

fof(f194,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4))
      | ~ r2_hidden(X4,X3) ) ),
    inference(resolution,[],[f183,f38])).

fof(f475,plain,
    ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f474])).

fof(f474,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(superposition,[],[f58,f78])).

fof(f78,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f500,plain,
    ( ~ spl4_5
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f494,f90,f70,f94])).

fof(f70,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f90,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f494,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f491,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f487,f61])).

fof(f487,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f479,f63])).

fof(f479,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f410,f60])).

fof(f410,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl4_8
  <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f472,plain,
    ( spl4_8
    | ~ spl4_9
    | spl4_4 ),
    inference(avatar_split_clause,[],[f465,f90,f412,f408])).

fof(f465,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1))
    | spl4_4 ),
    inference(resolution,[],[f251,f392])).

fof(f392,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X10,X11)
      | r1_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f85,f380])).

fof(f380,plain,(
    ! [X0] : sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f377,f61])).

fof(f377,plain,(
    ! [X0] :
      ( sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f370,f63])).

fof(f370,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X1))
      | sK2(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) = X1 ) ),
    inference(resolution,[],[f330,f60])).

fof(f330,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0))
      | sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0))
      | sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0
      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f316,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,k1_zfmisc_1(X1)))
      | sK2(X0,k1_zfmisc_1(X1)) = X1
      | r1_xboole_0(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
      | r1_xboole_0(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f37,f64])).

fof(f316,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK2(k3_enumset1(X0,X0,X0,X0,X0),X1))
      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f146,f64])).

fof(f146,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(sK2(k3_enumset1(X0,X0,X0,X0,X0),X1)))
      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f142,f114])).

fof(f142,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k1_zfmisc_1(sK2(X2,X3)),X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f111,f61])).

fof(f111,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(sK2(X5,X6),X4)
      | r1_xboole_0(X5,X6)
      | ~ r1_xboole_0(k1_zfmisc_1(X4),X5) ) ),
    inference(resolution,[],[f84,f63])).

fof(f85,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK2(X8,X7),X6)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X8,X7) ) ),
    inference(resolution,[],[f38,f37])).

fof(f251,plain,
    ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))
    | spl4_4 ),
    inference(resolution,[],[f247,f112])).

fof(f247,plain,
    ( r1_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_4 ),
    inference(superposition,[],[f58,f239])).

fof(f239,plain,
    ( k1_zfmisc_1(sK1) = k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_4 ),
    inference(resolution,[],[f156,f92])).

fof(f92,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | k1_zfmisc_1(X0) = k5_xboole_0(k1_zfmisc_1(X0),k3_xboole_0(k1_zfmisc_1(X0),k3_enumset1(X1,X1,X1,X1,X1))) ) ),
    inference(resolution,[],[f125,f64])).

fof(f125,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))) = X3 ) ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f429,plain,
    ( spl4_1
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl4_1
    | spl4_9 ),
    inference(subsumption_resolution,[],[f427,f68])).

fof(f68,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f427,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl4_9 ),
    inference(resolution,[],[f414,f125])).

fof(f414,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f412])).

fof(f79,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f74,f70,f76])).

fof(f74,plain,
    ( sK0 != sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(inner_rewriting,[],[f56])).

fof(f56,plain,
    ( sK0 != sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f31,f54,f35,f54,f54])).

fof(f31,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f73,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f55,f70,f66])).

fof(f55,plain,
    ( sK0 = sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f32,f54,f35,f54,f54])).

fof(f32,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (1911)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (1915)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (1920)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (1919)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (1925)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1907)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (1904)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (1903)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (1907)Refutation not found, incomplete strategy% (1907)------------------------------
% 0.21/0.55  % (1907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1925)Refutation not found, incomplete strategy% (1925)------------------------------
% 0.21/0.55  % (1925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% 0.21/0.55  % (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1907)Memory used [KB]: 10746
% 0.21/0.55  % (1907)Time elapsed: 0.120 s
% 0.21/0.55  % (1907)------------------------------
% 0.21/0.55  % (1907)------------------------------
% 0.21/0.55  % (1915)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1915)Memory used [KB]: 1663
% 0.21/0.55  % (1915)Time elapsed: 0.123 s
% 0.21/0.55  % (1915)------------------------------
% 0.21/0.55  % (1915)------------------------------
% 0.21/0.55  % (1925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1925)Memory used [KB]: 6140
% 0.21/0.55  % (1925)Time elapsed: 0.124 s
% 0.21/0.55  % (1925)------------------------------
% 0.21/0.55  % (1925)------------------------------
% 0.21/0.55  % (1911)Refutation not found, incomplete strategy% (1911)------------------------------
% 0.21/0.55  % (1911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1912)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (1911)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1911)Memory used [KB]: 1663
% 0.21/0.56  % (1911)Time elapsed: 0.133 s
% 0.21/0.56  % (1911)------------------------------
% 0.21/0.56  % (1911)------------------------------
% 0.21/0.58  % (1901)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.58  % (1899)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.59  % (1903)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f578,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f73,f79,f429,f472,f491,f500,f524,f577])).
% 0.21/0.59  fof(f577,plain,(
% 0.21/0.59    spl4_5 | ~spl4_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f576])).
% 0.21/0.59  fof(f576,plain,(
% 0.21/0.59    $false | (spl4_5 | ~spl4_9)),
% 0.21/0.59    inference(subsumption_resolution,[],[f570,f96])).
% 0.21/0.59  fof(f96,plain,(
% 0.21/0.59    ~r1_tarski(sK1,sK0) | spl4_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f94])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    spl4_5 <=> r1_tarski(sK1,sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.59  fof(f570,plain,(
% 0.21/0.59    r1_tarski(sK1,sK0) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f565,f61])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(flattening,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f565,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK1,X0)) ) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f558,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.59    inference(rectify,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.59  fof(f558,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK1,k1_zfmisc_1(X0)) | ~r1_tarski(sK0,X0)) ) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f529,f104])).
% 0.21/0.59  fof(f104,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~r1_tarski(X0,X2) | r2_hidden(X1,k1_zfmisc_1(X2))) )),
% 0.21/0.59    inference(resolution,[],[f83,f57])).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f39,f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f33,f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f34,f52])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f50,f51])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~r1_tarski(X2,X1)) )),
% 0.21/0.59    inference(resolution,[],[f38,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(rectify,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.59  fof(f529,plain,(
% 0.21/0.59    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f413,f128])).
% 0.21/0.59  fof(f128,plain,(
% 0.21/0.59    ( ! [X8,X9] : (~r2_hidden(X9,k3_enumset1(X8,X8,X8,X8,X8)) | r2_hidden(X8,k3_enumset1(X9,X9,X9,X9,X9))) )),
% 0.21/0.59    inference(resolution,[],[f114,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f49,f54])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.59  fof(f114,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 0.21/0.59    inference(resolution,[],[f112,f57])).
% 0.21/0.59  fof(f112,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.59  fof(f110,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.21/0.59    inference(resolution,[],[f84,f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X4,X5),X3) | ~r1_xboole_0(X3,X4) | r1_xboole_0(X4,X5)) )),
% 0.21/0.59    inference(resolution,[],[f38,f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f413,plain,(
% 0.21/0.59    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f412])).
% 0.21/0.59  fof(f412,plain,(
% 0.21/0.59    spl4_9 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.59  fof(f524,plain,(
% 0.21/0.59    ~spl4_3),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f523])).
% 0.21/0.59  fof(f523,plain,(
% 0.21/0.59    $false | ~spl4_3),
% 0.21/0.59    inference(subsumption_resolution,[],[f512,f183])).
% 0.21/0.59  fof(f183,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.21/0.59    inference(resolution,[],[f177,f61])).
% 0.21/0.59  fof(f177,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.21/0.59    inference(resolution,[],[f161,f63])).
% 0.21/0.59  fof(f161,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.21/0.59    inference(resolution,[],[f115,f60])).
% 0.21/0.59  fof(f115,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.21/0.59    inference(resolution,[],[f113,f57])).
% 0.21/0.59  fof(f113,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(resolution,[],[f84,f36])).
% 0.21/0.59  fof(f512,plain,(
% 0.21/0.59    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 0.21/0.59    inference(resolution,[],[f475,f194])).
% 0.21/0.59  fof(f194,plain,(
% 0.21/0.59    ( ! [X4,X3] : (~r1_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4)) | ~r2_hidden(X4,X3)) )),
% 0.21/0.59    inference(resolution,[],[f183,f38])).
% 0.21/0.59  fof(f475,plain,(
% 0.21/0.59    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 0.21/0.59    inference(trivial_inequality_removal,[],[f474])).
% 0.21/0.59  fof(f474,plain,(
% 0.21/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 0.21/0.59    inference(superposition,[],[f58,f78])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl4_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f76])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    spl4_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f44,f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(nnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.59  fof(f500,plain,(
% 0.21/0.59    ~spl4_5 | spl4_2 | ~spl4_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f494,f90,f70,f94])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    spl4_2 <=> sK0 = sK1),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.59  fof(f90,plain,(
% 0.21/0.59    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.59  fof(f494,plain,(
% 0.21/0.59    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl4_4),
% 0.21/0.59    inference(resolution,[],[f91,f42])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f90])).
% 0.21/0.59  fof(f491,plain,(
% 0.21/0.59    ~spl4_8),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f490])).
% 0.21/0.59  fof(f490,plain,(
% 0.21/0.59    $false | ~spl4_8),
% 0.21/0.59    inference(subsumption_resolution,[],[f487,f61])).
% 0.21/0.59  fof(f487,plain,(
% 0.21/0.59    ~r1_tarski(sK1,sK1) | ~spl4_8),
% 0.21/0.59    inference(resolution,[],[f479,f63])).
% 0.21/0.59  fof(f479,plain,(
% 0.21/0.59    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~spl4_8),
% 0.21/0.59    inference(resolution,[],[f410,f60])).
% 0.21/0.59  fof(f410,plain,(
% 0.21/0.59    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1)) | ~spl4_8),
% 0.21/0.59    inference(avatar_component_clause,[],[f408])).
% 0.21/0.59  fof(f408,plain,(
% 0.21/0.59    spl4_8 <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.59  fof(f472,plain,(
% 0.21/0.59    spl4_8 | ~spl4_9 | spl4_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f465,f90,f412,f408])).
% 0.21/0.59  fof(f465,plain,(
% 0.21/0.59    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK1)) | spl4_4),
% 0.21/0.59    inference(resolution,[],[f251,f392])).
% 0.21/0.59  fof(f392,plain,(
% 0.21/0.59    ( ! [X10,X11] : (~r1_xboole_0(X11,k1_zfmisc_1(X10)) | ~r2_hidden(X10,X11) | r1_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),k1_zfmisc_1(X10))) )),
% 0.21/0.59    inference(superposition,[],[f85,f380])).
% 0.21/0.59  fof(f380,plain,(
% 0.21/0.59    ( ! [X0] : (sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f377,f61])).
% 0.21/0.59  fof(f377,plain,(
% 0.21/0.59    ( ! [X0] : (sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0 | ~r1_tarski(X0,X0)) )),
% 0.21/0.59    inference(resolution,[],[f370,f63])).
% 0.21/0.59  fof(f370,plain,(
% 0.21/0.59    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(X1)) | sK2(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) = X1) )),
% 0.21/0.59    inference(resolution,[],[f330,f60])).
% 0.21/0.59  fof(f330,plain,(
% 0.21/0.59    ( ! [X0] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) | sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f324])).
% 0.21/0.59  fof(f324,plain,(
% 0.21/0.59    ( ! [X0] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) | sK2(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) = X0 | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(resolution,[],[f316,f103])).
% 0.21/0.59  fof(f103,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,k1_zfmisc_1(X1))) | sK2(X0,k1_zfmisc_1(X1)) = X1 | r1_xboole_0(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.59    inference(resolution,[],[f82,f42])).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | r1_xboole_0(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.59    inference(resolution,[],[f37,f64])).
% 0.21/0.59  fof(f316,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X0,sK2(k3_enumset1(X0,X0,X0,X0,X0),X1)) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.59    inference(resolution,[],[f146,f64])).
% 0.21/0.59  fof(f146,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(sK2(k3_enumset1(X0,X0,X0,X0,X0),X1))) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.59    inference(resolution,[],[f142,f114])).
% 0.21/0.59  fof(f142,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r1_xboole_0(k1_zfmisc_1(sK2(X2,X3)),X2) | r1_xboole_0(X2,X3)) )),
% 0.21/0.59    inference(resolution,[],[f111,f61])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    ( ! [X6,X4,X5] : (~r1_tarski(sK2(X5,X6),X4) | r1_xboole_0(X5,X6) | ~r1_xboole_0(k1_zfmisc_1(X4),X5)) )),
% 0.21/0.59    inference(resolution,[],[f84,f63])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    ( ! [X6,X8,X7] : (~r2_hidden(sK2(X8,X7),X6) | ~r1_xboole_0(X6,X7) | r1_xboole_0(X8,X7)) )),
% 0.21/0.59    inference(resolution,[],[f38,f37])).
% 0.21/0.59  fof(f251,plain,(
% 0.21/0.59    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) | spl4_4),
% 0.21/0.59    inference(resolution,[],[f247,f112])).
% 0.21/0.59  fof(f247,plain,(
% 0.21/0.59    r1_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_4),
% 0.21/0.59    inference(trivial_inequality_removal,[],[f246])).
% 0.21/0.59  fof(f246,plain,(
% 0.21/0.59    k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) | r1_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_4),
% 0.21/0.59    inference(superposition,[],[f58,f239])).
% 0.21/0.59  fof(f239,plain,(
% 0.21/0.59    k1_zfmisc_1(sK1) = k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_4),
% 0.21/0.59    inference(resolution,[],[f156,f92])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    ~r1_tarski(sK0,sK1) | spl4_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f90])).
% 0.21/0.59  fof(f156,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | k1_zfmisc_1(X0) = k5_xboole_0(k1_zfmisc_1(X0),k3_xboole_0(k1_zfmisc_1(X0),k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.21/0.59    inference(resolution,[],[f125,f64])).
% 0.21/0.59  fof(f125,plain,(
% 0.21/0.59    ( ! [X2,X3] : (r2_hidden(X2,X3) | k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))) = X3) )),
% 0.21/0.59    inference(resolution,[],[f114,f59])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.59    inference(definition_unfolding,[],[f43,f35])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f429,plain,(
% 0.21/0.59    spl4_1 | spl4_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f428])).
% 1.62/0.59  fof(f428,plain,(
% 1.62/0.59    $false | (spl4_1 | spl4_9)),
% 1.62/0.59    inference(subsumption_resolution,[],[f427,f68])).
% 1.62/0.59  fof(f68,plain,(
% 1.62/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl4_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f66])).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    spl4_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.59  fof(f427,plain,(
% 1.62/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl4_9),
% 1.62/0.59    inference(resolution,[],[f414,f125])).
% 1.62/0.59  fof(f414,plain,(
% 1.62/0.59    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_9),
% 1.62/0.59    inference(avatar_component_clause,[],[f412])).
% 1.62/0.59  fof(f79,plain,(
% 1.62/0.59    spl4_3 | ~spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f74,f70,f76])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    sK0 != sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.62/0.59    inference(inner_rewriting,[],[f56])).
% 1.62/0.59  fof(f56,plain,(
% 1.62/0.59    sK0 != sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.62/0.59    inference(definition_unfolding,[],[f31,f54,f35,f54,f54])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.62/0.59    inference(nnf_transformation,[],[f15])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.62/0.59    inference(ennf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.62/0.59    inference(negated_conjecture,[],[f12])).
% 1.62/0.59  fof(f12,conjecture,(
% 1.62/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.62/0.59  fof(f73,plain,(
% 1.62/0.59    ~spl4_1 | spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f55,f70,f66])).
% 1.62/0.59  fof(f55,plain,(
% 1.62/0.59    sK0 = sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.62/0.59    inference(definition_unfolding,[],[f32,f54,f35,f54,f54])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (1903)------------------------------
% 1.62/0.59  % (1903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (1903)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (1903)Memory used [KB]: 11129
% 1.62/0.59  % (1903)Time elapsed: 0.153 s
% 1.62/0.59  % (1903)------------------------------
% 1.62/0.59  % (1903)------------------------------
% 1.62/0.59  % (1896)Success in time 0.233 s
%------------------------------------------------------------------------------
