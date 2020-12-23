%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 570 expanded)
%              Number of leaves         :   32 ( 192 expanded)
%              Depth                    :   16
%              Number of atoms          :  381 (1772 expanded)
%              Number of equality atoms :  117 ( 516 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f96,f361,f732,f751,f759,f1108,f1157,f1238,f1239,f1492,f1501,f1558])).

fof(f1558,plain,
    ( spl4_15
    | ~ spl4_11
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f1556,f1490,f359,f757])).

fof(f757,plain,
    ( spl4_15
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f359,plain,
    ( spl4_11
  <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1490,plain,
    ( spl4_39
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1556,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl4_11
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f1528,f158])).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f156,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f90,f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f115,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f109,f72])).

fof(f72,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f43,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f156,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f76,f74])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1528,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_39 ),
    inference(superposition,[],[f360,f1491])).

fof(f1491,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f1490])).

fof(f360,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f359])).

fof(f1501,plain,(
    ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f1499])).

fof(f1499,plain,
    ( $false
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f1494,f1495])).

fof(f1495,plain,
    ( ! [X1] : ~ r2_hidden(sK3(sK1,sK0,k1_xboole_0),X1)
    | ~ spl4_38 ),
    inference(resolution,[],[f1488,f105])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f80,f103])).

fof(f103,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(global_subsumption,[],[f45,f101])).

fof(f101,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f55,f72])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1488,plain,
    ( r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f1487,plain,
    ( spl4_38
  <=> r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1494,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,sK0,k1_xboole_0),X0)
    | ~ spl4_38 ),
    inference(resolution,[],[f1488,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f81,f142])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1492,plain,
    ( spl4_38
    | spl4_39
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f1485,f1103,f1490,f1487])).

fof(f1103,plain,
    ( spl4_28
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1485,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f1482])).

fof(f1482,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_28 ),
    inference(resolution,[],[f1455,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1455,plain,
    ( ! [X25] :
        ( r2_hidden(sK3(sK1,X25,k1_xboole_0),sK0)
        | k1_xboole_0 = k4_xboole_0(sK1,X25) )
    | ~ spl4_28 ),
    inference(resolution,[],[f1091,f1128])).

fof(f1128,plain,
    ( ! [X28] :
        ( ~ r2_hidden(X28,sK1)
        | r2_hidden(X28,sK0) )
    | ~ spl4_28 ),
    inference(superposition,[],[f81,f1104])).

fof(f1104,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1091,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,k1_xboole_0),X1)
      | k1_xboole_0 = k4_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f1090,f142])).

fof(f1090,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1) ) ),
    inference(forward_demodulation,[],[f1089,f142])).

fof(f1089,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1) ) ),
    inference(duplicate_literal_removal,[],[f1084])).

fof(f1084,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1) ) ),
    inference(resolution,[],[f171,f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,k4_xboole_0(X2,X3)),X2)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
      | r2_hidden(sK3(X0,X1,k4_xboole_0(X2,X3)),X0) ) ),
    inference(resolution,[],[f65,f81])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f171,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK3(X4,X5,k4_xboole_0(X6,X7)),X7)
      | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5)
      | r2_hidden(sK3(X4,X5,k4_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f65,f80])).

fof(f1239,plain,
    ( spl4_28
    | ~ spl4_32
    | spl4_33
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f1227,f1106,f1152,f1149,f1103])).

fof(f1149,plain,
    ( spl4_32
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1152,plain,
    ( spl4_33
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1106,plain,
    ( spl4_29
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1227,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0)
    | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_29 ),
    inference(resolution,[],[f1107,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1107,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f1106])).

fof(f1238,plain,
    ( ~ spl4_29
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1234,f1152,f1106])).

fof(f1234,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1)
    | ~ spl4_33 ),
    inference(resolution,[],[f1153,f80])).

fof(f1153,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f1152])).

fof(f1157,plain,
    ( spl4_28
    | ~ spl4_2
    | spl4_32 ),
    inference(avatar_split_clause,[],[f1155,f1149,f87,f1103])).

fof(f87,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1155,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_2
    | spl4_32 ),
    inference(resolution,[],[f1150,f854])).

fof(f854,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0,sK1),sK0)
        | sK1 = k4_xboole_0(sK0,X0) )
    | ~ spl4_2 ),
    inference(factoring,[],[f847])).

fof(f847,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,sK1),sK0)
        | k4_xboole_0(X0,X1) = sK1
        | r2_hidden(sK3(X0,X1,sK1),X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f173,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f173,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | k4_xboole_0(X12,X13) = X14
      | r2_hidden(sK3(X12,X13,X14),X15)
      | r2_hidden(sK3(X12,X13,X14),X12) ) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1150,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1108,plain,
    ( spl4_28
    | spl4_29
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1098,f87,f1106,f1103])).

fof(f1098,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1)
    | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(factoring,[],[f1050])).

fof(f1050,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),sK1)
        | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
        | r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),X0) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f1043])).

fof(f1043,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),X0)
        | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
        | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
        | r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f858,f66])).

fof(f858,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,sK1),k4_xboole_0(sK0,X1))
        | r2_hidden(sK3(sK0,X0,sK1),X1)
        | sK1 = k4_xboole_0(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f854,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f759,plain,
    ( ~ spl4_15
    | spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f755,f743,f94,f757])).

fof(f94,plain,
    ( spl4_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f743,plain,
    ( spl4_13
  <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f755,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f95,f744])).

fof(f744,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f743])).

% (987)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f95,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f751,plain,
    ( spl4_13
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f750,f730,f359,f743])).

fof(f730,plain,
    ( spl4_12
  <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f750,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f740,f360])).

fof(f740,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f200,f731])).

fof(f731,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f730])).

fof(f200,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f154,f76])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f76,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f68,f68])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f732,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f726,f87,f730])).

fof(f726,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f340,f88])).

fof(f340,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k5_xboole_0(X4,k4_xboole_0(X3,X4)) = k4_subset_1(X3,X4,X3) ) ),
    inference(resolution,[],[f91,f90])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f361,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f345,f87,f359])).

fof(f345,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f338,f90])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(X0,k4_xboole_0(sK1,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f91,f88])).

fof(f96,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f92,f83,f94])).

fof(f83,plain,
    ( spl4_1
  <=> k3_subset_1(sK0,k1_xboole_0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f92,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl4_1 ),
    inference(forward_demodulation,[],[f84,f72])).

fof(f84,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f89,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f85,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f71,f83])).

fof(f71,plain,(
    k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f42,f70,f70])).

fof(f42,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (985)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.46  % (988)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.46  % (974)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (956)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (956)Refutation not found, incomplete strategy% (956)------------------------------
% 0.21/0.52  % (956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (956)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (956)Memory used [KB]: 1663
% 0.21/0.52  % (956)Time elapsed: 0.099 s
% 0.21/0.52  % (956)------------------------------
% 0.21/0.52  % (956)------------------------------
% 0.21/0.52  % (973)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (963)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (958)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (990)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (960)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (964)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (992)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (994)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (975)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (959)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (975)Refutation not found, incomplete strategy% (975)------------------------------
% 0.21/0.54  % (975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (975)Memory used [KB]: 10618
% 0.21/0.54  % (975)Time elapsed: 0.133 s
% 0.21/0.54  % (975)------------------------------
% 0.21/0.54  % (975)------------------------------
% 0.21/0.55  % (1001)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (991)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1000)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (983)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (986)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (962)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (984)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (983)Refutation not found, incomplete strategy% (983)------------------------------
% 0.21/0.55  % (983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (962)Refutation not found, incomplete strategy% (962)------------------------------
% 0.21/0.55  % (962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (962)Memory used [KB]: 6268
% 0.21/0.55  % (962)Time elapsed: 0.116 s
% 0.21/0.55  % (962)------------------------------
% 0.21/0.55  % (962)------------------------------
% 0.21/0.55  % (986)Refutation not found, incomplete strategy% (986)------------------------------
% 0.21/0.55  % (986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (986)Memory used [KB]: 10746
% 0.21/0.55  % (986)Time elapsed: 0.147 s
% 0.21/0.55  % (986)------------------------------
% 0.21/0.55  % (986)------------------------------
% 0.21/0.55  % (980)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (977)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (976)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (985)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (977)Refutation not found, incomplete strategy% (977)------------------------------
% 0.21/0.56  % (977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (977)Memory used [KB]: 10746
% 0.21/0.56  % (977)Time elapsed: 0.150 s
% 0.21/0.56  % (977)------------------------------
% 0.21/0.56  % (977)------------------------------
% 0.21/0.56  % (979)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (976)Refutation not found, incomplete strategy% (976)------------------------------
% 0.21/0.56  % (976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (976)Memory used [KB]: 10618
% 0.21/0.56  % (976)Time elapsed: 0.150 s
% 0.21/0.56  % (976)------------------------------
% 0.21/0.56  % (976)------------------------------
% 0.21/0.57  % (995)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (983)Memory used [KB]: 10618
% 0.21/0.57  % (983)Time elapsed: 0.150 s
% 0.21/0.57  % (983)------------------------------
% 0.21/0.57  % (983)------------------------------
% 1.64/0.57  % (978)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f1582,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(avatar_sat_refutation,[],[f85,f89,f96,f361,f732,f751,f759,f1108,f1157,f1238,f1239,f1492,f1501,f1558])).
% 1.64/0.57  fof(f1558,plain,(
% 1.64/0.57    spl4_15 | ~spl4_11 | ~spl4_39),
% 1.64/0.57    inference(avatar_split_clause,[],[f1556,f1490,f359,f757])).
% 1.64/0.57  fof(f757,plain,(
% 1.64/0.57    spl4_15 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.64/0.57  fof(f359,plain,(
% 1.64/0.57    spl4_11 <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.64/0.57  fof(f1490,plain,(
% 1.64/0.57    spl4_39 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.64/0.57  fof(f1556,plain,(
% 1.64/0.57    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl4_11 | ~spl4_39)),
% 1.64/0.57    inference(forward_demodulation,[],[f1528,f158])).
% 1.64/0.57  fof(f158,plain,(
% 1.64/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.57    inference(forward_demodulation,[],[f156,f142])).
% 1.64/0.57  fof(f142,plain,(
% 1.64/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.64/0.57    inference(global_subsumption,[],[f90,f140])).
% 1.64/0.57  fof(f140,plain,(
% 1.64/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(superposition,[],[f115,f55])).
% 1.64/0.57  fof(f55,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f26,plain,(
% 1.64/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.57    inference(ennf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,axiom,(
% 1.64/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.64/0.57  fof(f115,plain,(
% 1.64/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f109,f72])).
% 1.64/0.57  fof(f72,plain,(
% 1.64/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.64/0.57    inference(definition_unfolding,[],[f44,f70])).
% 1.64/0.57  fof(f70,plain,(
% 1.64/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f47,f43])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,axiom,(
% 1.64/0.57    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.64/0.57  fof(f47,plain,(
% 1.64/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f18])).
% 1.64/0.57  fof(f18,axiom,(
% 1.64/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,axiom,(
% 1.64/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.64/0.57  fof(f109,plain,(
% 1.64/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.64/0.57    inference(resolution,[],[f56,f45])).
% 1.64/0.57  fof(f45,plain,(
% 1.64/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f19])).
% 1.64/0.57  fof(f19,axiom,(
% 1.64/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.64/0.57  fof(f56,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.64/0.57    inference(cnf_transformation,[],[f27])).
% 1.64/0.57  fof(f27,plain,(
% 1.64/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.57    inference(ennf_transformation,[],[f15])).
% 1.64/0.57  fof(f15,axiom,(
% 1.64/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.64/0.57  fof(f90,plain,(
% 1.64/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f73,f72])).
% 1.64/0.57  fof(f73,plain,(
% 1.64/0.57    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f46,f70])).
% 1.64/0.57  fof(f46,plain,(
% 1.64/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f14])).
% 1.64/0.57  fof(f14,axiom,(
% 1.64/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.64/0.57  fof(f156,plain,(
% 1.64/0.57    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.64/0.57    inference(superposition,[],[f76,f74])).
% 1.64/0.57  fof(f74,plain,(
% 1.64/0.57    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.64/0.57    inference(definition_unfolding,[],[f48,f69])).
% 1.64/0.57  fof(f69,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f50,f68])).
% 1.64/0.57  fof(f68,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f51,f60])).
% 1.64/0.57  fof(f60,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f9])).
% 1.64/0.57  fof(f9,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.57  fof(f51,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f8])).
% 1.64/0.57  fof(f8,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.57  fof(f50,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f10])).
% 1.64/0.57  fof(f10,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.64/0.57  fof(f48,plain,(
% 1.64/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f22])).
% 1.64/0.57  fof(f22,plain,(
% 1.64/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.64/0.57    inference(rectify,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.64/0.57  fof(f76,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f53,f69])).
% 1.64/0.57  fof(f53,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.64/0.57  fof(f1528,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | (~spl4_11 | ~spl4_39)),
% 1.64/0.57    inference(superposition,[],[f360,f1491])).
% 1.64/0.57  fof(f1491,plain,(
% 1.64/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl4_39),
% 1.64/0.57    inference(avatar_component_clause,[],[f1490])).
% 1.64/0.57  fof(f360,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl4_11),
% 1.64/0.57    inference(avatar_component_clause,[],[f359])).
% 1.64/0.57  fof(f1501,plain,(
% 1.64/0.57    ~spl4_38),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f1499])).
% 1.64/0.57  fof(f1499,plain,(
% 1.64/0.57    $false | ~spl4_38),
% 1.64/0.57    inference(subsumption_resolution,[],[f1494,f1495])).
% 1.64/0.57  fof(f1495,plain,(
% 1.64/0.57    ( ! [X1] : (~r2_hidden(sK3(sK1,sK0,k1_xboole_0),X1)) ) | ~spl4_38),
% 1.64/0.57    inference(resolution,[],[f1488,f105])).
% 1.64/0.57  fof(f105,plain,(
% 1.64/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X2)) )),
% 1.64/0.57    inference(superposition,[],[f80,f103])).
% 1.64/0.57  fof(f103,plain,(
% 1.64/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.57    inference(global_subsumption,[],[f45,f101])).
% 1.64/0.57  fof(f101,plain,(
% 1.64/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(superposition,[],[f55,f72])).
% 1.64/0.57  fof(f80,plain,(
% 1.64/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.64/0.57    inference(equality_resolution,[],[f63])).
% 1.64/0.57  fof(f63,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f40,plain,(
% 1.64/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.64/0.57  fof(f39,plain,(
% 1.64/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.57    inference(rectify,[],[f37])).
% 1.64/0.57  fof(f37,plain,(
% 1.64/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.57    inference(flattening,[],[f36])).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.57    inference(nnf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.64/0.57  fof(f1488,plain,(
% 1.64/0.57    r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0) | ~spl4_38),
% 1.64/0.57    inference(avatar_component_clause,[],[f1487])).
% 1.64/0.57  fof(f1487,plain,(
% 1.64/0.57    spl4_38 <=> r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.64/0.57  fof(f1494,plain,(
% 1.64/0.57    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,k1_xboole_0),X0)) ) | ~spl4_38),
% 1.64/0.57    inference(resolution,[],[f1488,f143])).
% 1.64/0.57  fof(f143,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 1.64/0.57    inference(superposition,[],[f81,f142])).
% 1.64/0.57  fof(f81,plain,(
% 1.64/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.64/0.57    inference(equality_resolution,[],[f62])).
% 1.64/0.57  fof(f62,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f1492,plain,(
% 1.64/0.57    spl4_38 | spl4_39 | ~spl4_28),
% 1.64/0.57    inference(avatar_split_clause,[],[f1485,f1103,f1490,f1487])).
% 1.64/0.57  fof(f1103,plain,(
% 1.64/0.57    spl4_28 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.64/0.57  fof(f1485,plain,(
% 1.64/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0) | r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0) | ~spl4_28),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f1482])).
% 1.64/0.57  fof(f1482,plain,(
% 1.64/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK0) | r2_hidden(sK3(sK1,sK0,k1_xboole_0),k1_xboole_0) | ~spl4_28),
% 1.64/0.57    inference(resolution,[],[f1455,f66])).
% 1.64/0.57  fof(f66,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f1455,plain,(
% 1.64/0.57    ( ! [X25] : (r2_hidden(sK3(sK1,X25,k1_xboole_0),sK0) | k1_xboole_0 = k4_xboole_0(sK1,X25)) ) | ~spl4_28),
% 1.64/0.57    inference(resolution,[],[f1091,f1128])).
% 1.64/0.57  fof(f1128,plain,(
% 1.64/0.57    ( ! [X28] : (~r2_hidden(X28,sK1) | r2_hidden(X28,sK0)) ) | ~spl4_28),
% 1.64/0.57    inference(superposition,[],[f81,f1104])).
% 1.64/0.57  fof(f1104,plain,(
% 1.64/0.57    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_28),
% 1.64/0.57    inference(avatar_component_clause,[],[f1103])).
% 1.64/0.57  fof(f1091,plain,(
% 1.64/0.57    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,k1_xboole_0),X1) | k1_xboole_0 = k4_xboole_0(X1,X2)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f1090,f142])).
% 1.64/0.57  fof(f1090,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f1089,f142])).
% 1.64/0.57  fof(f1089,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f1084])).
% 1.64/0.57  fof(f1084,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK3(X1,X2,k4_xboole_0(X0,X0)),X1)) )),
% 1.64/0.57    inference(resolution,[],[f171,f170])).
% 1.64/0.57  fof(f170,plain,(
% 1.64/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0,X1,k4_xboole_0(X2,X3)),X2) | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3) | r2_hidden(sK3(X0,X1,k4_xboole_0(X2,X3)),X0)) )),
% 1.64/0.57    inference(resolution,[],[f65,f81])).
% 1.64/0.57  fof(f65,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f171,plain,(
% 1.64/0.57    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,X5,k4_xboole_0(X6,X7)),X7) | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5) | r2_hidden(sK3(X4,X5,k4_xboole_0(X6,X7)),X4)) )),
% 1.64/0.57    inference(resolution,[],[f65,f80])).
% 1.64/0.57  fof(f1239,plain,(
% 1.64/0.57    spl4_28 | ~spl4_32 | spl4_33 | ~spl4_29),
% 1.64/0.57    inference(avatar_split_clause,[],[f1227,f1106,f1152,f1149,f1103])).
% 1.64/0.57  fof(f1149,plain,(
% 1.64/0.57    spl4_32 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.64/0.57  fof(f1152,plain,(
% 1.64/0.57    spl4_33 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.64/0.57  fof(f1106,plain,(
% 1.64/0.57    spl4_29 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.64/0.57  fof(f1227,plain,(
% 1.64/0.57    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_29),
% 1.64/0.57    inference(resolution,[],[f1107,f67])).
% 1.64/0.57  fof(f67,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f1107,plain,(
% 1.64/0.57    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1) | ~spl4_29),
% 1.64/0.57    inference(avatar_component_clause,[],[f1106])).
% 1.64/0.57  fof(f1238,plain,(
% 1.64/0.57    ~spl4_29 | ~spl4_33),
% 1.64/0.57    inference(avatar_split_clause,[],[f1234,f1152,f1106])).
% 1.64/0.57  fof(f1234,plain,(
% 1.64/0.57    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1) | ~spl4_33),
% 1.64/0.57    inference(resolution,[],[f1153,f80])).
% 1.64/0.57  fof(f1153,plain,(
% 1.64/0.57    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) | ~spl4_33),
% 1.64/0.57    inference(avatar_component_clause,[],[f1152])).
% 1.64/0.57  fof(f1157,plain,(
% 1.64/0.57    spl4_28 | ~spl4_2 | spl4_32),
% 1.64/0.57    inference(avatar_split_clause,[],[f1155,f1149,f87,f1103])).
% 1.64/0.57  fof(f87,plain,(
% 1.64/0.57    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.64/0.57  fof(f1155,plain,(
% 1.64/0.57    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl4_2 | spl4_32)),
% 1.64/0.57    inference(resolution,[],[f1150,f854])).
% 1.64/0.57  fof(f854,plain,(
% 1.64/0.57    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),sK0) | sK1 = k4_xboole_0(sK0,X0)) ) | ~spl4_2),
% 1.64/0.57    inference(factoring,[],[f847])).
% 1.64/0.57  fof(f847,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),sK0) | k4_xboole_0(X0,X1) = sK1 | r2_hidden(sK3(X0,X1,sK1),X0)) ) | ~spl4_2),
% 1.64/0.57    inference(resolution,[],[f173,f88])).
% 1.64/0.57  fof(f88,plain,(
% 1.64/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.64/0.57    inference(avatar_component_clause,[],[f87])).
% 1.64/0.57  fof(f173,plain,(
% 1.64/0.57    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X14,k1_zfmisc_1(X15)) | k4_xboole_0(X12,X13) = X14 | r2_hidden(sK3(X12,X13,X14),X15) | r2_hidden(sK3(X12,X13,X14),X12)) )),
% 1.64/0.57    inference(resolution,[],[f65,f57])).
% 1.64/0.57  fof(f57,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f28])).
% 1.64/0.57  fof(f28,plain,(
% 1.64/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.57    inference(ennf_transformation,[],[f16])).
% 1.64/0.57  fof(f16,axiom,(
% 1.64/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.64/0.57  fof(f1150,plain,(
% 1.64/0.57    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK0) | spl4_32),
% 1.64/0.57    inference(avatar_component_clause,[],[f1149])).
% 1.64/0.57  fof(f1108,plain,(
% 1.64/0.57    spl4_28 | spl4_29 | ~spl4_2),
% 1.64/0.57    inference(avatar_split_clause,[],[f1098,f87,f1106,f1103])).
% 1.64/0.57  fof(f1098,plain,(
% 1.64/0.57    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),sK1),sK1) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.64/0.57    inference(factoring,[],[f1050])).
% 1.64/0.57  fof(f1050,plain,(
% 1.64/0.57    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),sK1) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),X0)) ) | ~spl4_2),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f1043])).
% 1.64/0.57  fof(f1043,plain,(
% 1.64/0.57    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),X0) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,X0),sK1),sK1)) ) | ~spl4_2),
% 1.64/0.57    inference(resolution,[],[f858,f66])).
% 1.64/0.57  fof(f858,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,sK1),k4_xboole_0(sK0,X1)) | r2_hidden(sK3(sK0,X0,sK1),X1) | sK1 = k4_xboole_0(sK0,X0)) ) | ~spl4_2),
% 1.64/0.57    inference(resolution,[],[f854,f79])).
% 1.64/0.57  fof(f79,plain,(
% 1.64/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.64/0.57    inference(equality_resolution,[],[f64])).
% 1.64/0.57  fof(f64,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f759,plain,(
% 1.64/0.57    ~spl4_15 | spl4_3 | ~spl4_13),
% 1.64/0.57    inference(avatar_split_clause,[],[f755,f743,f94,f757])).
% 1.64/0.57  fof(f94,plain,(
% 1.64/0.57    spl4_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.64/0.57  fof(f743,plain,(
% 1.64/0.57    spl4_13 <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.64/0.57  fof(f755,plain,(
% 1.64/0.57    sK0 != k4_subset_1(sK0,sK0,sK1) | (spl4_3 | ~spl4_13)),
% 1.64/0.57    inference(superposition,[],[f95,f744])).
% 1.64/0.57  fof(f744,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | ~spl4_13),
% 1.64/0.57    inference(avatar_component_clause,[],[f743])).
% 1.64/0.57  % (987)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.57  fof(f95,plain,(
% 1.64/0.57    sK0 != k4_subset_1(sK0,sK1,sK0) | spl4_3),
% 1.64/0.57    inference(avatar_component_clause,[],[f94])).
% 1.64/0.57  fof(f751,plain,(
% 1.64/0.57    spl4_13 | ~spl4_11 | ~spl4_12),
% 1.64/0.57    inference(avatar_split_clause,[],[f750,f730,f359,f743])).
% 1.64/0.57  fof(f730,plain,(
% 1.64/0.57    spl4_12 <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.64/0.57  fof(f750,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | (~spl4_11 | ~spl4_12)),
% 1.64/0.57    inference(forward_demodulation,[],[f740,f360])).
% 1.64/0.57  fof(f740,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl4_12),
% 1.64/0.57    inference(superposition,[],[f200,f731])).
% 1.64/0.57  fof(f731,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl4_12),
% 1.64/0.57    inference(avatar_component_clause,[],[f730])).
% 1.64/0.57  fof(f200,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 1.64/0.57    inference(superposition,[],[f154,f76])).
% 1.64/0.57  fof(f154,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.64/0.57    inference(superposition,[],[f76,f75])).
% 1.64/0.57  fof(f75,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f49,f68,f68])).
% 1.64/0.57  fof(f49,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f7])).
% 1.64/0.57  fof(f7,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.64/0.57  fof(f732,plain,(
% 1.64/0.57    spl4_12 | ~spl4_2),
% 1.64/0.57    inference(avatar_split_clause,[],[f726,f87,f730])).
% 1.64/0.57  fof(f726,plain,(
% 1.64/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.64/0.57    inference(resolution,[],[f340,f88])).
% 1.64/0.57  fof(f340,plain,(
% 1.64/0.57    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | k5_xboole_0(X4,k4_xboole_0(X3,X4)) = k4_subset_1(X3,X4,X3)) )),
% 1.64/0.57    inference(resolution,[],[f91,f90])).
% 1.64/0.57  fof(f91,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f78,f76])).
% 1.64/0.57  fof(f78,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f61,f69])).
% 1.64/0.57  fof(f61,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f31])).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.57    inference(flattening,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.64/0.58    inference(ennf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.64/0.58  fof(f361,plain,(
% 1.64/0.58    spl4_11 | ~spl4_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f345,f87,f359])).
% 1.64/0.58  fof(f345,plain,(
% 1.64/0.58    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl4_2),
% 1.64/0.58    inference(resolution,[],[f338,f90])).
% 1.64/0.58  fof(f338,plain,(
% 1.64/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(X0,k4_xboole_0(sK1,X0))) ) | ~spl4_2),
% 1.64/0.58    inference(resolution,[],[f91,f88])).
% 1.64/0.58  fof(f96,plain,(
% 1.64/0.58    ~spl4_3 | spl4_1),
% 1.64/0.58    inference(avatar_split_clause,[],[f92,f83,f94])).
% 1.64/0.58  fof(f83,plain,(
% 1.64/0.58    spl4_1 <=> k3_subset_1(sK0,k1_xboole_0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.64/0.58  fof(f92,plain,(
% 1.64/0.58    sK0 != k4_subset_1(sK0,sK1,sK0) | spl4_1),
% 1.64/0.58    inference(forward_demodulation,[],[f84,f72])).
% 1.64/0.58  fof(f84,plain,(
% 1.64/0.58    k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0)) | spl4_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f83])).
% 1.64/0.58  fof(f89,plain,(
% 1.64/0.58    spl4_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f41,f87])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.64/0.58    inference(cnf_transformation,[],[f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f21])).
% 1.64/0.58  fof(f21,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.64/0.58    inference(negated_conjecture,[],[f20])).
% 1.64/0.58  fof(f20,conjecture,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.64/0.58  fof(f85,plain,(
% 1.64/0.58    ~spl4_1),
% 1.64/0.58    inference(avatar_split_clause,[],[f71,f83])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,k1_xboole_0))),
% 1.64/0.58    inference(definition_unfolding,[],[f42,f70,f70])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.64/0.58    inference(cnf_transformation,[],[f33])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (985)------------------------------
% 1.64/0.58  % (985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (985)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (985)Memory used [KB]: 11769
% 1.64/0.58  % (985)Time elapsed: 0.162 s
% 1.64/0.58  % (985)------------------------------
% 1.64/0.58  % (985)------------------------------
% 1.64/0.58  % (987)Refutation not found, incomplete strategy% (987)------------------------------
% 1.64/0.58  % (987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (987)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (987)Memory used [KB]: 1663
% 1.64/0.58  % (987)Time elapsed: 0.168 s
% 1.64/0.58  % (987)------------------------------
% 1.64/0.58  % (987)------------------------------
% 1.64/0.58  % (982)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.64/0.58  % (949)Success in time 0.214 s
%------------------------------------------------------------------------------
