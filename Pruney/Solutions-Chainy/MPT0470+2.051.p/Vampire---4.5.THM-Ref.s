%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 269 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 ( 670 expanded)
%              Number of equality atoms :   40 ( 130 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f168,f171,f191,f212,f228,f235,f248,f367,f371])).

fof(f371,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | spl3_17 ),
    inference(avatar_split_clause,[],[f369,f359,f201,f162])).

fof(f162,plain,
    ( spl3_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f201,plain,
    ( spl3_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f359,plain,
    ( spl3_17
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f369,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl3_17 ),
    inference(resolution,[],[f361,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f361,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f359])).

fof(f367,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f355,f189,f209,f62,f359])).

fof(f62,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f209,plain,
    ( spl3_8
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f189,plain,
    ( spl3_5
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f355,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f87,f347])).

fof(f347,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f331,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f331,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X3)) )
    | ~ spl3_5 ),
    inference(resolution,[],[f190,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f75,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f58,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f190,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f189])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f84,f54])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f82,f75])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f248,plain,
    ( ~ spl3_6
    | ~ spl3_3
    | spl3_9 ),
    inference(avatar_split_clause,[],[f246,f216,f162,f201])).

fof(f216,plain,
    ( spl3_9
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f246,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl3_9 ),
    inference(resolution,[],[f218,f59])).

fof(f218,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f216])).

fof(f235,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f41,f203])).

fof(f203,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f228,plain,
    ( ~ spl3_9
    | spl3_2
    | ~ spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f198,f166,f209,f66,f216])).

fof(f66,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f166,plain,
    ( spl3_4
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f198,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(superposition,[],[f92,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(resolution,[],[f175,f41])).

fof(f175,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X3,k1_xboole_0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f167,f83])).

fof(f167,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f73,f85])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f212,plain,
    ( ~ spl3_6
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f194,f166,f209,f201])).

fof(f194,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f167,f185])).

fof(f191,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f187,f189,f162])).

fof(f187,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f50,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f171,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f43,f169])).

fof(f169,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_3 ),
    inference(resolution,[],[f164,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f164,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f162])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f168,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f160,f166,f162])).

fof(f160,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f66,f62])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:19:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (8898)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.45  % (8898)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f372,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f69,f168,f171,f191,f212,f228,f235,f248,f367,f371])).
% 0.22/0.45  fof(f371,plain,(
% 0.22/0.45    ~spl3_3 | ~spl3_6 | spl3_17),
% 0.22/0.45    inference(avatar_split_clause,[],[f369,f359,f201,f162])).
% 0.22/0.45  fof(f162,plain,(
% 0.22/0.45    spl3_3 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f201,plain,(
% 0.22/0.45    spl3_6 <=> v1_relat_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f359,plain,(
% 0.22/0.45    spl3_17 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.45  fof(f369,plain,(
% 0.22/0.45    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl3_17),
% 0.22/0.45    inference(resolution,[],[f361,f59])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.45  fof(f361,plain,(
% 0.22/0.45    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl3_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f359])).
% 0.22/0.45  fof(f367,plain,(
% 0.22/0.45    ~spl3_17 | spl3_1 | ~spl3_8 | ~spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f355,f189,f209,f62,f359])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f209,plain,(
% 0.22/0.45    spl3_8 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    spl3_5 <=> ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f355,plain,(
% 0.22/0.45    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_5),
% 0.22/0.45    inference(superposition,[],[f87,f347])).
% 0.22/0.45  fof(f347,plain,(
% 0.22/0.45    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_5),
% 0.22/0.45    inference(resolution,[],[f331,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f16])).
% 0.22/0.45  fof(f16,conjecture,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.45  fof(f331,plain,(
% 0.22/0.45    ( ! [X3] : (~v1_relat_1(X3) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X3))) ) | ~spl3_5),
% 0.22/0.45    inference(resolution,[],[f190,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.45    inference(resolution,[],[f82,f77])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.45    inference(resolution,[],[f76,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~r1_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(resolution,[],[f75,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(rectify,[],[f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(superposition,[],[f58,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.45    inference(rectify,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_tarski(X1,k1_xboole_0)) )),
% 0.22/0.45    inference(superposition,[],[f60,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f189])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(resolution,[],[f72,f85])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(resolution,[],[f84,f54])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X2,X1)) )),
% 0.22/0.45    inference(resolution,[],[f82,f75])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.45    inference(resolution,[],[f51,f48])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.45  fof(f248,plain,(
% 0.22/0.45    ~spl3_6 | ~spl3_3 | spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f246,f216,f162,f201])).
% 0.22/0.45  fof(f216,plain,(
% 0.22/0.45    spl3_9 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f246,plain,(
% 0.22/0.45    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl3_9),
% 0.22/0.45    inference(resolution,[],[f218,f59])).
% 0.22/0.45  fof(f218,plain,(
% 0.22/0.45    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f216])).
% 0.22/0.45  fof(f235,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.45  fof(f234,plain,(
% 0.22/0.45    $false | spl3_6),
% 0.22/0.45    inference(subsumption_resolution,[],[f41,f203])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    ~v1_relat_1(sK0) | spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f201])).
% 0.22/0.45  fof(f228,plain,(
% 0.22/0.45    ~spl3_9 | spl3_2 | ~spl3_8 | ~spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f198,f166,f209,f66,f216])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl3_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    spl3_4 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.22/0.45    inference(superposition,[],[f92,f185])).
% 0.22/0.45  fof(f185,plain,(
% 0.22/0.45    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f175,f41])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    ( ! [X3] : (~v1_relat_1(X3) | k1_xboole_0 = k2_relat_1(k5_relat_1(X3,k1_xboole_0))) ) | ~spl3_4),
% 0.22/0.46    inference(resolution,[],[f167,f83])).
% 0.22/0.46  fof(f167,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f166])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_xboole_0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(resolution,[],[f73,f85])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(resolution,[],[f52,f48])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k2_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.46    inference(flattening,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.46  fof(f212,plain,(
% 0.22/0.46    ~spl3_6 | spl3_8 | ~spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f194,f166,f209,f201])).
% 0.22/0.46  fof(f194,plain,(
% 0.22/0.46    r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK0) | ~spl3_4),
% 0.22/0.46    inference(superposition,[],[f167,f185])).
% 0.22/0.46  fof(f191,plain,(
% 0.22/0.46    ~spl3_3 | spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f187,f189,f162])).
% 0.22/0.46  fof(f187,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.46    inference(superposition,[],[f50,f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,axiom,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.46  fof(f171,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.46  fof(f170,plain,(
% 0.22/0.46    $false | spl3_3),
% 0.22/0.46    inference(subsumption_resolution,[],[f43,f169])).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | spl3_3),
% 0.22/0.46    inference(resolution,[],[f164,f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    ~v1_relat_1(k1_xboole_0) | spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f162])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f168,plain,(
% 0.22/0.46    ~spl3_3 | spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f160,f166,f162])).
% 0.22/0.46  fof(f160,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(superposition,[],[f49,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    ~spl3_1 | ~spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f66,f62])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f34])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (8898)------------------------------
% 0.22/0.46  % (8898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (8898)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (8898)Memory used [KB]: 6268
% 0.22/0.46  % (8898)Time elapsed: 0.012 s
% 0.22/0.46  % (8898)------------------------------
% 0.22/0.46  % (8898)------------------------------
% 0.22/0.46  % (8881)Success in time 0.097 s
%------------------------------------------------------------------------------
