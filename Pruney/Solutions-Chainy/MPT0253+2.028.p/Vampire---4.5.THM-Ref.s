%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 150 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :    7
%              Number of atoms          :  233 ( 356 expanded)
%              Number of equality atoms :   67 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f710,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f71,f75,f79,f87,f91,f103,f120,f128,f142,f146,f150,f253,f266,f690,f695,f709])).

fof(f709,plain,
    ( spl3_3
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | spl3_3
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f66,f697])).

fof(f697,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(unit_resulting_resolution,[],[f252,f694])).

fof(f694,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X1,X2) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl3_44
  <=> ! [X1,X2] :
        ( k2_xboole_0(X1,X2) = X2
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f252,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_28
  <=> r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f66,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_3
  <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f695,plain,
    ( spl3_44
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f691,f688,f264,f144,f126,f693])).

fof(f126,plain,
    ( spl3_16
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f144,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f264,plain,
    ( spl3_30
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f688,plain,
    ( spl3_43
  <=> ! [X1,X2] :
        ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f691,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X1,X2) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f689,f271])).

fof(f271,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f268,f127])).

fof(f127,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f268,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl3_19
    | ~ spl3_30 ),
    inference(superposition,[],[f145,f265])).

fof(f265,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f264])).

fof(f145,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f689,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f688])).

fof(f690,plain,
    ( spl3_43
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f178,f140,f101,f85,f688])).

fof(f85,plain,
    ( spl3_8
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f140,plain,
    ( spl3_18
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f178,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f168,f86])).

fof(f86,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f168,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X1)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f141,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f141,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f266,plain,
    ( spl3_30
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f137,f118,f89,f77,f73,f264])).

fof(f73,plain,
    ( spl3_5
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( spl3_6
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( spl3_9
  <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f118,plain,
    ( spl3_15
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f137,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f133,f116])).

fof(f116,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f90,f74])).

fof(f74,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f90,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f133,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f119,f78])).

fof(f78,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f119,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f253,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f203,f148,f59,f54,f250])).

fof(f54,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f148,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f56,f61,f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f61,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f56,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f150,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f48,f148])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f146,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f45,f144])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f142,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f42,f140])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f128,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f85,f69,f126])).

fof(f69,plain,
    ( spl3_4
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f86,f70])).

fof(f70,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f120,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f41,f118])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f103,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f91,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f87,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f79,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f71,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f67,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (31737)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (31738)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (31751)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (31744)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (31741)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (31742)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (31743)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (31749)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (31752)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (31754)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (31746)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (31745)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (31739)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (31753)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (31748)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (31742)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (31750)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (31740)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (31747)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f710,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f57,f62,f67,f71,f75,f79,f87,f91,f103,f120,f128,f142,f146,f150,f253,f266,f690,f695,f709])).
% 0.22/0.52  fof(f709,plain,(
% 0.22/0.52    spl3_3 | ~spl3_28 | ~spl3_44),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f708])).
% 0.22/0.52  fof(f708,plain,(
% 0.22/0.52    $false | (spl3_3 | ~spl3_28 | ~spl3_44)),
% 0.22/0.52    inference(subsumption_resolution,[],[f66,f697])).
% 0.22/0.52  fof(f697,plain,(
% 0.22/0.52    sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | (~spl3_28 | ~spl3_44)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f252,f694])).
% 0.22/0.52  fof(f694,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = X2 | ~r1_tarski(X1,X2)) ) | ~spl3_44),
% 0.22/0.52    inference(avatar_component_clause,[],[f693])).
% 0.22/0.52  fof(f693,plain,(
% 0.22/0.52    spl3_44 <=> ! [X1,X2] : (k2_xboole_0(X1,X2) = X2 | ~r1_tarski(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    r1_tarski(k2_tarski(sK0,sK2),sK1) | ~spl3_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f250])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    spl3_28 <=> r1_tarski(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) | spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl3_3 <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f695,plain,(
% 0.22/0.52    spl3_44 | ~spl3_16 | ~spl3_19 | ~spl3_30 | ~spl3_43),
% 0.22/0.52    inference(avatar_split_clause,[],[f691,f688,f264,f144,f126,f693])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl3_16 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    spl3_19 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl3_30 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.52  fof(f688,plain,(
% 0.22/0.52    spl3_43 <=> ! [X1,X2] : (k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.52  fof(f691,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = X2 | ~r1_tarski(X1,X2)) ) | (~spl3_16 | ~spl3_19 | ~spl3_30 | ~spl3_43)),
% 0.22/0.52    inference(forward_demodulation,[],[f689,f271])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl3_16 | ~spl3_19 | ~spl3_30)),
% 0.22/0.52    inference(forward_demodulation,[],[f268,f127])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl3_19 | ~spl3_30)),
% 0.22/0.52    inference(superposition,[],[f145,f265])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl3_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f144])).
% 0.22/0.52  fof(f689,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2)) ) | ~spl3_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f688])).
% 0.22/0.52  fof(f690,plain,(
% 0.22/0.52    spl3_43 | ~spl3_8 | ~spl3_12 | ~spl3_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f178,f140,f101,f85,f688])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl3_8 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl3_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl3_18 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2)) ) | (~spl3_8 | ~spl3_12 | ~spl3_18)),
% 0.22/0.52    inference(forward_demodulation,[],[f168,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f85])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X1) | ~r1_tarski(X1,X2)) ) | (~spl3_12 | ~spl3_18)),
% 0.22/0.52    inference(superposition,[],[f141,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    spl3_30 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f137,f118,f89,f77,f73,f264])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl3_5 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl3_6 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl3_9 <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl3_15 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f133,f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_5 | ~spl3_9)),
% 0.22/0.52    inference(superposition,[],[f90,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) ) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) ) | (~spl3_6 | ~spl3_15)),
% 0.22/0.52    inference(superposition,[],[f119,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl3_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    spl3_28 | ~spl3_1 | ~spl3_2 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f203,f148,f59,f54,f250])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl3_20 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    r1_tarski(k2_tarski(sK0,sK2),sK1) | (~spl3_1 | ~spl3_2 | ~spl3_20)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f56,f61,f149])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) ) | ~spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f148])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f59])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f148])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f144])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl3_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f140])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl3_16 | ~spl3_4 | ~spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f112,f85,f69,f126])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl3_4 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_4 | ~spl3_8)),
% 0.22/0.52    inference(superposition,[],[f86,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    spl3_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f118])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f101])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f38,f89])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f37,f85])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f77])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    inference(rectify,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.52    inference(rectify,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f33,f69])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f64])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.52    inference(negated_conjecture,[],[f19])).
% 0.22/0.52  fof(f19,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f59])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    r2_hidden(sK2,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f54])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (31742)------------------------------
% 0.22/0.52  % (31742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31742)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (31742)Memory used [KB]: 6780
% 0.22/0.52  % (31742)Time elapsed: 0.074 s
% 0.22/0.52  % (31742)------------------------------
% 0.22/0.52  % (31742)------------------------------
% 0.22/0.52  % (31736)Success in time 0.164 s
%------------------------------------------------------------------------------
