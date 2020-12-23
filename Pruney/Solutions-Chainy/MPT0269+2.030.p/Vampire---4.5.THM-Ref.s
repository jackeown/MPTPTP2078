%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:51 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 201 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 ( 435 expanded)
%              Number of equality atoms :   96 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f836,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f134,f157,f249,f577,f613,f642,f649,f831,f835])).

fof(f835,plain,
    ( ~ spl3_12
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f248,f830,f634])).

fof(f634,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl3_16 ),
    inference(superposition,[],[f78,f611])).

fof(f611,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl3_16
  <=> k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f830,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f828])).

fof(f828,plain,
    ( spl3_28
  <=> r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f248,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl3_12
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f831,plain,
    ( spl3_18
    | spl3_28
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f821,f639,f828,f646])).

fof(f646,plain,
    ( spl3_18
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f639,plain,
    ( spl3_17
  <=> r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f821,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f234,f641])).

fof(f641,plain,
    ( r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f639])).

fof(f234,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k2_enumset1(X3,X3,X3,X3))
      | r2_hidden(X3,X2)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f66,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f36,f52,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f649,plain,
    ( spl3_7
    | ~ spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f628,f609,f646,f154])).

fof(f154,plain,
    ( spl3_7
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f628,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f69,f611])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f642,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f632,f609,f639])).

fof(f632,plain,
    ( r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_16 ),
    inference(superposition,[],[f76,f611])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f613,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f603,f574,f609])).

fof(f574,plain,
    ( spl3_14
  <=> k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f603,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_14 ),
    inference(superposition,[],[f165,f576])).

fof(f576,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f574])).

fof(f165,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f161,f97])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f64,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f161,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f59,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f577,plain,
    ( spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f295,f93,f574])).

fof(f93,plain,
    ( spl3_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f295,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f60,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f52,f52])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f249,plain,
    ( spl3_12
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f233,f93,f83,f246])).

fof(f83,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f233,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f66,f95])).

fof(f157,plain,
    ( ~ spl3_7
    | spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f135,f131,f88,f154])).

fof(f88,plain,
    ( spl3_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f131,plain,
    ( spl3_6
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f135,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f133,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f133,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f128,f93,f131])).

fof(f128,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f69,f95])).

fof(f96,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f63,f93])).

fof(f63,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f30,f52,f58])).

fof(f30,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f91,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f62,f88])).

fof(f62,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f32,f58])).

fof(f32,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (7495)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (7512)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (7491)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (7491)Refutation not found, incomplete strategy% (7491)------------------------------
% 0.21/0.53  % (7491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7491)Memory used [KB]: 1663
% 0.21/0.53  % (7491)Time elapsed: 0.107 s
% 0.21/0.53  % (7491)------------------------------
% 0.21/0.53  % (7491)------------------------------
% 0.21/0.53  % (7513)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (7498)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (7505)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (7519)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (7501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (7493)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (7492)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7490)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (7521)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7521)Refutation not found, incomplete strategy% (7521)------------------------------
% 0.21/0.54  % (7521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7521)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7521)Memory used [KB]: 1663
% 0.21/0.54  % (7521)Time elapsed: 0.001 s
% 0.21/0.54  % (7521)------------------------------
% 0.21/0.54  % (7521)------------------------------
% 0.21/0.54  % (7496)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (7499)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (7518)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (7494)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (7509)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (7517)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (7515)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (7520)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (7514)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (7504)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (7508)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (7511)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (7506)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (7506)Refutation not found, incomplete strategy% (7506)------------------------------
% 0.21/0.56  % (7506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7506)Memory used [KB]: 10618
% 0.21/0.56  % (7506)Time elapsed: 0.137 s
% 0.21/0.56  % (7506)------------------------------
% 0.21/0.56  % (7506)------------------------------
% 0.21/0.56  % (7503)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (7502)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (7502)Refutation not found, incomplete strategy% (7502)------------------------------
% 0.21/0.56  % (7502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7502)Memory used [KB]: 10618
% 0.21/0.56  % (7502)Time elapsed: 0.139 s
% 0.21/0.56  % (7502)------------------------------
% 0.21/0.56  % (7502)------------------------------
% 0.21/0.56  % (7497)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.56  % (7500)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.56  % (7507)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.56  % (7517)Refutation not found, incomplete strategy% (7517)------------------------------
% 1.44/0.56  % (7517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (7517)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (7517)Memory used [KB]: 6268
% 1.44/0.56  % (7517)Time elapsed: 0.149 s
% 1.44/0.56  % (7517)------------------------------
% 1.44/0.56  % (7517)------------------------------
% 1.44/0.57  % (7515)Refutation not found, incomplete strategy% (7515)------------------------------
% 1.44/0.57  % (7515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (7515)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (7515)Memory used [KB]: 10746
% 1.44/0.57  % (7515)Time elapsed: 0.147 s
% 1.44/0.57  % (7515)------------------------------
% 1.44/0.57  % (7515)------------------------------
% 1.64/0.61  % (7514)Refutation found. Thanks to Tanya!
% 1.64/0.61  % SZS status Theorem for theBenchmark
% 1.64/0.61  % SZS output start Proof for theBenchmark
% 1.64/0.61  fof(f836,plain,(
% 1.64/0.61    $false),
% 1.64/0.61    inference(avatar_sat_refutation,[],[f86,f91,f96,f134,f157,f249,f577,f613,f642,f649,f831,f835])).
% 1.64/0.61  fof(f835,plain,(
% 1.64/0.61    ~spl3_12 | ~spl3_16 | ~spl3_28),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f832])).
% 1.64/0.61  fof(f832,plain,(
% 1.64/0.61    $false | (~spl3_12 | ~spl3_16 | ~spl3_28)),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f248,f830,f634])).
% 1.64/0.61  fof(f634,plain,(
% 1.64/0.61    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~r2_hidden(X4,sK0)) ) | ~spl3_16),
% 1.64/0.61    inference(superposition,[],[f78,f611])).
% 1.64/0.61  fof(f611,plain,(
% 1.64/0.61    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_16),
% 1.64/0.61    inference(avatar_component_clause,[],[f609])).
% 1.64/0.61  fof(f609,plain,(
% 1.64/0.61    spl3_16 <=> k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.64/0.61  fof(f78,plain,(
% 1.64/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.64/0.61    inference(equality_resolution,[],[f74])).
% 1.64/0.61  fof(f74,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.64/0.61    inference(definition_unfolding,[],[f42,f52])).
% 1.64/0.61  fof(f52,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f5])).
% 1.64/0.61  fof(f5,axiom,(
% 1.64/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.64/0.61  fof(f42,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.61    inference(cnf_transformation,[],[f27])).
% 1.64/0.61  fof(f27,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.64/0.61  fof(f26,plain,(
% 1.64/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(rectify,[],[f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(flattening,[],[f23])).
% 1.64/0.61  fof(f23,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(nnf_transformation,[],[f1])).
% 1.64/0.61  fof(f1,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.64/0.61  fof(f830,plain,(
% 1.64/0.61    r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~spl3_28),
% 1.64/0.61    inference(avatar_component_clause,[],[f828])).
% 1.64/0.61  fof(f828,plain,(
% 1.64/0.61    spl3_28 <=> r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.64/0.61  fof(f248,plain,(
% 1.64/0.61    r2_hidden(sK1,sK0) | ~spl3_12),
% 1.64/0.61    inference(avatar_component_clause,[],[f246])).
% 1.64/0.61  fof(f246,plain,(
% 1.64/0.61    spl3_12 <=> r2_hidden(sK1,sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.64/0.61  fof(f831,plain,(
% 1.64/0.61    spl3_18 | spl3_28 | ~spl3_17),
% 1.64/0.61    inference(avatar_split_clause,[],[f821,f639,f828,f646])).
% 1.64/0.61  fof(f646,plain,(
% 1.64/0.61    spl3_18 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.64/0.61  fof(f639,plain,(
% 1.64/0.61    spl3_17 <=> r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.64/0.61  fof(f821,plain,(
% 1.64/0.61    r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_17),
% 1.64/0.61    inference(resolution,[],[f234,f641])).
% 1.64/0.61  fof(f641,plain,(
% 1.64/0.61    r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_17),
% 1.64/0.61    inference(avatar_component_clause,[],[f639])).
% 1.64/0.61  fof(f234,plain,(
% 1.64/0.61    ( ! [X2,X3] : (~r1_tarski(X2,k2_enumset1(X3,X3,X3,X3)) | r2_hidden(X3,X2) | k1_xboole_0 = X2) )),
% 1.64/0.61    inference(superposition,[],[f66,f68])).
% 1.64/0.61  fof(f68,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f39,f52])).
% 1.64/0.61  fof(f39,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f22])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.64/0.61    inference(nnf_transformation,[],[f4])).
% 1.64/0.61  fof(f4,axiom,(
% 1.64/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.64/0.61  fof(f66,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f36,f52,f58])).
% 1.64/0.61  fof(f58,plain,(
% 1.64/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f37,f57])).
% 1.64/0.61  fof(f57,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f47,f54])).
% 1.64/0.61  fof(f54,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f14])).
% 1.64/0.61  fof(f14,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.61  fof(f47,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f13])).
% 1.64/0.61  fof(f13,axiom,(
% 1.64/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.61  fof(f37,plain,(
% 1.64/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f12])).
% 1.64/0.61  fof(f12,axiom,(
% 1.64/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.61  fof(f36,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f21,plain,(
% 1.64/0.61    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.64/0.61    inference(nnf_transformation,[],[f15])).
% 1.64/0.61  fof(f15,axiom,(
% 1.64/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.64/0.61  fof(f649,plain,(
% 1.64/0.61    spl3_7 | ~spl3_18 | ~spl3_16),
% 1.64/0.61    inference(avatar_split_clause,[],[f628,f609,f646,f154])).
% 1.64/0.61  fof(f154,plain,(
% 1.64/0.61    spl3_7 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.64/0.61  fof(f628,plain,(
% 1.64/0.61    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_16),
% 1.64/0.61    inference(superposition,[],[f69,f611])).
% 1.64/0.61  fof(f69,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f38,f52])).
% 1.64/0.61  fof(f38,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f22])).
% 1.64/0.61  fof(f642,plain,(
% 1.64/0.61    spl3_17 | ~spl3_16),
% 1.64/0.61    inference(avatar_split_clause,[],[f632,f609,f639])).
% 1.64/0.61  fof(f632,plain,(
% 1.64/0.61    r1_tarski(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_16),
% 1.64/0.61    inference(superposition,[],[f76,f611])).
% 1.64/0.61  fof(f76,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f51,f52])).
% 1.64/0.61  fof(f51,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f7])).
% 1.64/0.61  fof(f7,axiom,(
% 1.64/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.64/0.61  fof(f613,plain,(
% 1.64/0.61    spl3_16 | ~spl3_14),
% 1.64/0.61    inference(avatar_split_clause,[],[f603,f574,f609])).
% 1.64/0.61  fof(f574,plain,(
% 1.64/0.61    spl3_14 <=> k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.64/0.61  fof(f603,plain,(
% 1.64/0.61    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_14),
% 1.64/0.61    inference(superposition,[],[f165,f576])).
% 1.64/0.61  fof(f576,plain,(
% 1.64/0.61    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0) | ~spl3_14),
% 1.64/0.61    inference(avatar_component_clause,[],[f574])).
% 1.64/0.61  fof(f165,plain,(
% 1.64/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.64/0.61    inference(forward_demodulation,[],[f161,f97])).
% 1.64/0.61  fof(f97,plain,(
% 1.64/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.61    inference(forward_demodulation,[],[f64,f40])).
% 1.64/0.61  fof(f40,plain,(
% 1.64/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f6])).
% 1.64/0.61  fof(f6,axiom,(
% 1.64/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.64/0.61  fof(f64,plain,(
% 1.64/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.64/0.61    inference(definition_unfolding,[],[f33,f52])).
% 1.64/0.61  fof(f33,plain,(
% 1.64/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f8])).
% 1.64/0.61  fof(f8,axiom,(
% 1.64/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.64/0.61  fof(f161,plain,(
% 1.64/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.64/0.61    inference(superposition,[],[f59,f65])).
% 1.64/0.61  fof(f65,plain,(
% 1.64/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f34,f52])).
% 1.64/0.61  fof(f34,plain,(
% 1.64/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,axiom,(
% 1.64/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.64/0.61  fof(f59,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f56,f52])).
% 1.64/0.61  fof(f56,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f11])).
% 1.64/0.61  fof(f11,axiom,(
% 1.64/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.64/0.61  fof(f577,plain,(
% 1.64/0.61    spl3_14 | ~spl3_3),
% 1.64/0.61    inference(avatar_split_clause,[],[f295,f93,f574])).
% 1.64/0.61  fof(f93,plain,(
% 1.64/0.61    spl3_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.64/0.61  fof(f295,plain,(
% 1.64/0.61    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),k1_xboole_0) | ~spl3_3),
% 1.64/0.61    inference(superposition,[],[f60,f95])).
% 1.64/0.61  fof(f95,plain,(
% 1.64/0.61    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl3_3),
% 1.64/0.61    inference(avatar_component_clause,[],[f93])).
% 1.64/0.61  fof(f60,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f55,f52,f52])).
% 1.64/0.61  fof(f55,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f2])).
% 1.64/0.61  fof(f2,axiom,(
% 1.64/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.64/0.61  fof(f249,plain,(
% 1.64/0.61    spl3_12 | spl3_1 | ~spl3_3),
% 1.64/0.61    inference(avatar_split_clause,[],[f233,f93,f83,f246])).
% 1.64/0.61  fof(f83,plain,(
% 1.64/0.61    spl3_1 <=> k1_xboole_0 = sK0),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.64/0.61  fof(f233,plain,(
% 1.64/0.61    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | ~spl3_3),
% 1.64/0.61    inference(superposition,[],[f66,f95])).
% 1.64/0.61  fof(f157,plain,(
% 1.64/0.61    ~spl3_7 | spl3_2 | ~spl3_6),
% 1.64/0.61    inference(avatar_split_clause,[],[f135,f131,f88,f154])).
% 1.64/0.61  fof(f88,plain,(
% 1.64/0.61    spl3_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.64/0.61  fof(f131,plain,(
% 1.64/0.61    spl3_6 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.64/0.61  fof(f135,plain,(
% 1.64/0.61    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_6),
% 1.64/0.61    inference(resolution,[],[f133,f50])).
% 1.64/0.61  fof(f50,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f29])).
% 1.64/0.61  fof(f29,plain,(
% 1.64/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.61    inference(flattening,[],[f28])).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.61    inference(nnf_transformation,[],[f3])).
% 1.64/0.61  fof(f3,axiom,(
% 1.64/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.61  fof(f133,plain,(
% 1.64/0.61    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_6),
% 1.64/0.61    inference(avatar_component_clause,[],[f131])).
% 1.64/0.61  fof(f134,plain,(
% 1.64/0.61    spl3_6 | ~spl3_3),
% 1.64/0.61    inference(avatar_split_clause,[],[f128,f93,f131])).
% 1.64/0.61  fof(f128,plain,(
% 1.64/0.61    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_3),
% 1.64/0.61    inference(trivial_inequality_removal,[],[f124])).
% 1.64/0.61  fof(f124,plain,(
% 1.64/0.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_3),
% 1.64/0.61    inference(superposition,[],[f69,f95])).
% 1.64/0.61  fof(f96,plain,(
% 1.64/0.61    spl3_3),
% 1.64/0.61    inference(avatar_split_clause,[],[f63,f93])).
% 1.64/0.61  fof(f63,plain,(
% 1.64/0.61    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.64/0.61    inference(definition_unfolding,[],[f30,f52,f58])).
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f20,plain,(
% 1.64/0.61    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 1.64/0.61  fof(f19,plain,(
% 1.64/0.61    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f18,plain,(
% 1.64/0.61    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.64/0.61    inference(ennf_transformation,[],[f17])).
% 1.64/0.61  fof(f17,negated_conjecture,(
% 1.64/0.61    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.64/0.61    inference(negated_conjecture,[],[f16])).
% 1.64/0.61  fof(f16,conjecture,(
% 1.64/0.61    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.64/0.61  fof(f91,plain,(
% 1.64/0.61    ~spl3_2),
% 1.64/0.61    inference(avatar_split_clause,[],[f62,f88])).
% 1.64/0.61  fof(f62,plain,(
% 1.64/0.61    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.64/0.61    inference(definition_unfolding,[],[f32,f58])).
% 1.64/0.61  fof(f32,plain,(
% 1.64/0.61    sK0 != k1_tarski(sK1)),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f86,plain,(
% 1.64/0.61    ~spl3_1),
% 1.64/0.61    inference(avatar_split_clause,[],[f31,f83])).
% 1.64/0.61  fof(f31,plain,(
% 1.64/0.61    k1_xboole_0 != sK0),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (7514)------------------------------
% 1.64/0.61  % (7514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (7514)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (7514)Memory used [KB]: 11257
% 1.64/0.61  % (7514)Time elapsed: 0.161 s
% 1.64/0.61  % (7514)------------------------------
% 1.64/0.61  % (7514)------------------------------
% 1.64/0.61  % (7483)Success in time 0.24 s
%------------------------------------------------------------------------------
