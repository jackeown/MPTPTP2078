%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 172 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 ( 411 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f396,f917,f1107,f1146,f1266,f1295,f1350])).

fof(f1350,plain,(
    spl5_33 ),
    inference(avatar_contradiction_clause,[],[f1347])).

fof(f1347,plain,
    ( $false
    | spl5_33 ),
    inference(resolution,[],[f1291,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1291,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_33 ),
    inference(resolution,[],[f1261,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1261,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1259,plain,
    ( spl5_33
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1295,plain,
    ( ~ spl5_11
    | spl5_34 ),
    inference(avatar_contradiction_clause,[],[f1292])).

fof(f1292,plain,
    ( $false
    | ~ spl5_11
    | spl5_34 ),
    inference(resolution,[],[f1265,f1188])).

fof(f1188,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_11 ),
    inference(trivial_inequality_removal,[],[f1160])).

fof(f1160,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ spl5_11 ),
    inference(superposition,[],[f196,f376])).

fof(f376,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl5_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f196,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1265,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1263,plain,
    ( spl5_34
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1266,plain,
    ( ~ spl5_33
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f179,f1263,f1259])).

fof(f179,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1146,plain,
    ( spl5_12
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f1143])).

fof(f1143,plain,
    ( $false
    | spl5_12
    | ~ spl5_15 ),
    inference(resolution,[],[f825,f755])).

fof(f755,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f754])).

fof(f754,plain,
    ( spl5_15
  <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f825,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl5_12 ),
    inference(resolution,[],[f198,f557])).

fof(f557,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl5_12 ),
    inference(resolution,[],[f380,f48])).

fof(f380,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl5_12
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f198,plain,(
    ! [X10,X8,X9] :
      ( r1_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X8)))
      | ~ r1_xboole_0(X10,X8) ) ),
    inference(superposition,[],[f72,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f1107,plain,
    ( spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f1103])).

fof(f1103,plain,
    ( $false
    | spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f847,f760])).

fof(f760,plain,
    ( r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f759])).

fof(f759,plain,
    ( spl5_16
  <=> r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

% (29581)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f847,plain,
    ( ~ r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_15 ),
    inference(resolution,[],[f756,f48])).

fof(f756,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f754])).

fof(f917,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f914])).

fof(f914,plain,
    ( $false
    | spl5_16 ),
    inference(resolution,[],[f911,f36])).

fof(f911,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_16 ),
    inference(resolution,[],[f908,f48])).

fof(f908,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_16 ),
    inference(resolution,[],[f907,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f907,plain,
    ( r2_hidden(sK3,sK1)
    | spl5_16 ),
    inference(resolution,[],[f238,f761])).

fof(f761,plain,
    ( ~ r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f759])).

fof(f238,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f39,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f396,plain,
    ( spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f395,f379,f375])).

fof(f395,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f145,f63])).

fof(f63,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f34,f43,f62])).

fof(f34,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f145,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (29578)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (29571)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (29572)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (29575)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (29583)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (29574)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (29584)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (29582)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (29585)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (29586)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (29580)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (29579)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (29576)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (29573)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (29570)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (29590)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (29574)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 1.25/0.51  fof(f1351,plain,(
% 1.25/0.51    $false),
% 1.25/0.51    inference(avatar_sat_refutation,[],[f396,f917,f1107,f1146,f1266,f1295,f1350])).
% 1.25/0.51  fof(f1350,plain,(
% 1.25/0.51    spl5_33),
% 1.25/0.51    inference(avatar_contradiction_clause,[],[f1347])).
% 1.25/0.51  fof(f1347,plain,(
% 1.25/0.51    $false | spl5_33),
% 1.25/0.51    inference(resolution,[],[f1291,f36])).
% 1.25/0.51  fof(f36,plain,(
% 1.25/0.51    r1_xboole_0(sK2,sK1)),
% 1.25/0.51    inference(cnf_transformation,[],[f28])).
% 1.25/0.51  fof(f28,plain,(
% 1.25/0.51    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.25/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).
% 1.25/0.51  fof(f27,plain,(
% 1.25/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.25/0.51    introduced(choice_axiom,[])).
% 1.25/0.51  fof(f21,plain,(
% 1.25/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.25/0.51    inference(flattening,[],[f20])).
% 1.25/0.51  fof(f20,plain,(
% 1.25/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.25/0.51    inference(ennf_transformation,[],[f18])).
% 1.25/0.51  fof(f18,negated_conjecture,(
% 1.25/0.51    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.25/0.51    inference(negated_conjecture,[],[f17])).
% 1.25/0.51  fof(f17,conjecture,(
% 1.25/0.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.25/0.51  fof(f1291,plain,(
% 1.25/0.51    ~r1_xboole_0(sK2,sK1) | spl5_33),
% 1.25/0.51    inference(resolution,[],[f1261,f48])).
% 1.25/0.51  fof(f48,plain,(
% 1.25/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f24])).
% 1.25/0.51  fof(f24,plain,(
% 1.25/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.25/0.51    inference(ennf_transformation,[],[f3])).
% 1.25/0.51  fof(f3,axiom,(
% 1.25/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.25/0.51  fof(f1261,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,sK2) | spl5_33),
% 1.25/0.51    inference(avatar_component_clause,[],[f1259])).
% 1.25/0.51  fof(f1259,plain,(
% 1.25/0.51    spl5_33 <=> r1_xboole_0(sK1,sK2)),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.25/0.51  fof(f1295,plain,(
% 1.25/0.51    ~spl5_11 | spl5_34),
% 1.25/0.51    inference(avatar_contradiction_clause,[],[f1292])).
% 1.25/0.51  fof(f1292,plain,(
% 1.25/0.51    $false | (~spl5_11 | spl5_34)),
% 1.25/0.51    inference(resolution,[],[f1265,f1188])).
% 1.25/0.51  fof(f1188,plain,(
% 1.25/0.51    r1_xboole_0(sK1,sK0) | ~spl5_11),
% 1.25/0.51    inference(trivial_inequality_removal,[],[f1160])).
% 1.25/0.51  fof(f1160,plain,(
% 1.25/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl5_11),
% 1.25/0.51    inference(superposition,[],[f196,f376])).
% 1.25/0.51  fof(f376,plain,(
% 1.25/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_11),
% 1.25/0.51    inference(avatar_component_clause,[],[f375])).
% 1.25/0.51  fof(f375,plain,(
% 1.25/0.51    spl5_11 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.25/0.51  fof(f196,plain,(
% 1.25/0.51    ( ! [X4,X5] : (k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 1.25/0.51    inference(superposition,[],[f67,f64])).
% 1.25/0.51  fof(f64,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.25/0.51    inference(definition_unfolding,[],[f40,f43,f43])).
% 1.25/0.51  fof(f43,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.25/0.51    inference(cnf_transformation,[],[f7])).
% 1.25/0.51  fof(f7,axiom,(
% 1.25/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.25/0.51  fof(f40,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f1])).
% 1.25/0.51  fof(f1,axiom,(
% 1.25/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.25/0.51  fof(f67,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f52,f43])).
% 1.25/0.51  fof(f52,plain,(
% 1.25/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.25/0.51    inference(cnf_transformation,[],[f32])).
% 1.25/0.51  fof(f32,plain,(
% 1.25/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.25/0.51    inference(nnf_transformation,[],[f2])).
% 1.25/0.51  fof(f2,axiom,(
% 1.25/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.25/0.51  fof(f1265,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,sK0) | spl5_34),
% 1.25/0.51    inference(avatar_component_clause,[],[f1263])).
% 1.25/0.51  fof(f1263,plain,(
% 1.25/0.51    spl5_34 <=> r1_xboole_0(sK1,sK0)),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.25/0.51  fof(f1266,plain,(
% 1.25/0.51    ~spl5_33 | ~spl5_34),
% 1.25/0.51    inference(avatar_split_clause,[],[f179,f1263,f1259])).
% 1.25/0.51  fof(f179,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.25/0.51    inference(resolution,[],[f57,f73])).
% 1.25/0.51  fof(f73,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.25/0.51    inference(resolution,[],[f48,f37])).
% 1.25/0.51  fof(f37,plain,(
% 1.25/0.51    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.25/0.51    inference(cnf_transformation,[],[f28])).
% 1.25/0.51  fof(f57,plain,(
% 1.25/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f25])).
% 1.25/0.51  fof(f25,plain,(
% 1.25/0.51    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.25/0.51    inference(ennf_transformation,[],[f8])).
% 1.25/0.51  fof(f8,axiom,(
% 1.25/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.25/0.51  fof(f1146,plain,(
% 1.25/0.51    spl5_12 | ~spl5_15),
% 1.25/0.51    inference(avatar_contradiction_clause,[],[f1143])).
% 1.25/0.51  fof(f1143,plain,(
% 1.25/0.51    $false | (spl5_12 | ~spl5_15)),
% 1.25/0.51    inference(resolution,[],[f825,f755])).
% 1.25/0.51  fof(f755,plain,(
% 1.25/0.51    r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | ~spl5_15),
% 1.25/0.51    inference(avatar_component_clause,[],[f754])).
% 1.25/0.51  fof(f754,plain,(
% 1.25/0.51    spl5_15 <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.25/0.51  fof(f825,plain,(
% 1.25/0.51    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl5_12),
% 1.25/0.51    inference(resolution,[],[f198,f557])).
% 1.25/0.51  fof(f557,plain,(
% 1.25/0.51    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl5_12),
% 1.25/0.51    inference(resolution,[],[f380,f48])).
% 1.25/0.51  fof(f380,plain,(
% 1.25/0.51    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_12),
% 1.25/0.51    inference(avatar_component_clause,[],[f379])).
% 1.25/0.51  fof(f379,plain,(
% 1.25/0.51    spl5_12 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.25/0.51  fof(f198,plain,(
% 1.25/0.51    ( ! [X10,X8,X9] : (r1_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X8))) | ~r1_xboole_0(X10,X8)) )),
% 1.25/0.51    inference(superposition,[],[f72,f64])).
% 1.25/0.51  fof(f72,plain,(
% 1.25/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f60,f43])).
% 1.25/0.51  fof(f60,plain,(
% 1.25/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.25/0.51    inference(cnf_transformation,[],[f26])).
% 1.25/0.51  fof(f26,plain,(
% 1.25/0.51    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.25/0.51    inference(ennf_transformation,[],[f9])).
% 1.25/0.51  fof(f9,axiom,(
% 1.25/0.51    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.25/0.51  fof(f1107,plain,(
% 1.25/0.51    spl5_15 | ~spl5_16),
% 1.25/0.51    inference(avatar_contradiction_clause,[],[f1103])).
% 1.25/0.51  fof(f1103,plain,(
% 1.25/0.51    $false | (spl5_15 | ~spl5_16)),
% 1.25/0.51    inference(resolution,[],[f847,f760])).
% 1.25/0.51  fof(f760,plain,(
% 1.25/0.51    r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl5_16),
% 1.25/0.51    inference(avatar_component_clause,[],[f759])).
% 1.25/0.51  fof(f759,plain,(
% 1.25/0.51    spl5_16 <=> r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.25/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.25/0.51  % (29581)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.25/0.51  fof(f847,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_15),
% 1.25/0.51    inference(resolution,[],[f756,f48])).
% 1.25/0.51  fof(f756,plain,(
% 1.25/0.51    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl5_15),
% 1.25/0.51    inference(avatar_component_clause,[],[f754])).
% 1.25/0.51  fof(f917,plain,(
% 1.25/0.51    spl5_16),
% 1.25/0.51    inference(avatar_contradiction_clause,[],[f914])).
% 1.25/0.51  fof(f914,plain,(
% 1.25/0.51    $false | spl5_16),
% 1.25/0.51    inference(resolution,[],[f911,f36])).
% 1.25/0.51  fof(f911,plain,(
% 1.25/0.51    ~r1_xboole_0(sK2,sK1) | spl5_16),
% 1.25/0.51    inference(resolution,[],[f908,f48])).
% 1.25/0.51  fof(f908,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,sK2) | spl5_16),
% 1.25/0.51    inference(resolution,[],[f907,f106])).
% 1.25/0.51  fof(f106,plain,(
% 1.25/0.51    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.25/0.51    inference(resolution,[],[f46,f35])).
% 1.25/0.51  fof(f35,plain,(
% 1.25/0.51    r2_hidden(sK3,sK2)),
% 1.25/0.51    inference(cnf_transformation,[],[f28])).
% 1.25/0.51  fof(f46,plain,(
% 1.25/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f30])).
% 1.25/0.51  fof(f30,plain,(
% 1.25/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.25/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f29])).
% 1.25/0.51  fof(f29,plain,(
% 1.25/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.25/0.51    introduced(choice_axiom,[])).
% 1.25/0.51  fof(f22,plain,(
% 1.25/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.25/0.51    inference(ennf_transformation,[],[f19])).
% 1.25/0.51  fof(f19,plain,(
% 1.25/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.25/0.51    inference(rectify,[],[f4])).
% 1.25/0.51  fof(f4,axiom,(
% 1.25/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.25/0.51  fof(f907,plain,(
% 1.25/0.51    r2_hidden(sK3,sK1) | spl5_16),
% 1.25/0.51    inference(resolution,[],[f238,f761])).
% 1.25/0.51  fof(f761,plain,(
% 1.25/0.51    ~r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_16),
% 1.25/0.51    inference(avatar_component_clause,[],[f759])).
% 1.25/0.51  fof(f238,plain,(
% 1.25/0.51    ( ! [X2,X3] : (r1_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)) | r2_hidden(X3,X2)) )),
% 1.25/0.51    inference(superposition,[],[f39,f69])).
% 1.25/0.51  fof(f69,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f54,f62])).
% 1.25/0.51  fof(f62,plain,(
% 1.25/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f38,f61])).
% 1.25/0.51  fof(f61,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f42,f55])).
% 1.25/0.51  fof(f55,plain,(
% 1.25/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f15])).
% 1.25/0.51  fof(f15,axiom,(
% 1.25/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.51  fof(f42,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f14])).
% 1.25/0.51  fof(f14,axiom,(
% 1.25/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.51  fof(f38,plain,(
% 1.25/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f13])).
% 1.25/0.51  fof(f13,axiom,(
% 1.25/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.51  fof(f54,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f33])).
% 1.25/0.51  fof(f33,plain,(
% 1.25/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.25/0.51    inference(nnf_transformation,[],[f16])).
% 1.25/0.51  fof(f16,axiom,(
% 1.25/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.25/0.51  fof(f39,plain,(
% 1.25/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f10])).
% 1.25/0.51  fof(f10,axiom,(
% 1.25/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.25/0.51  fof(f396,plain,(
% 1.25/0.51    spl5_11 | ~spl5_12),
% 1.25/0.51    inference(avatar_split_clause,[],[f395,f379,f375])).
% 1.25/0.51  fof(f395,plain,(
% 1.25/0.51    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.25/0.51    inference(resolution,[],[f145,f63])).
% 1.25/0.51  fof(f63,plain,(
% 1.25/0.51    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.25/0.51    inference(definition_unfolding,[],[f34,f43,f62])).
% 1.25/0.51  fof(f34,plain,(
% 1.25/0.51    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.25/0.51    inference(cnf_transformation,[],[f28])).
% 1.25/0.51  fof(f145,plain,(
% 1.25/0.51    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 1.25/0.51    inference(superposition,[],[f68,f66])).
% 1.25/0.51  fof(f66,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f47,f43])).
% 1.25/0.51  fof(f47,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f23])).
% 1.25/0.51  fof(f23,plain,(
% 1.25/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.25/0.51    inference(ennf_transformation,[],[f6])).
% 1.25/0.51  fof(f6,axiom,(
% 1.25/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.25/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.25/0.51  fof(f68,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.25/0.51    inference(definition_unfolding,[],[f51,f43])).
% 1.25/0.51  fof(f51,plain,(
% 1.25/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.25/0.51    inference(cnf_transformation,[],[f32])).
% 1.25/0.51  % SZS output end Proof for theBenchmark
% 1.25/0.51  % (29574)------------------------------
% 1.25/0.51  % (29574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.51  % (29574)Termination reason: Refutation
% 1.25/0.51  
% 1.25/0.51  % (29574)Memory used [KB]: 6780
% 1.25/0.51  % (29574)Time elapsed: 0.077 s
% 1.25/0.51  % (29574)------------------------------
% 1.25/0.51  % (29574)------------------------------
% 1.25/0.52  % (29565)Success in time 0.158 s
%------------------------------------------------------------------------------
