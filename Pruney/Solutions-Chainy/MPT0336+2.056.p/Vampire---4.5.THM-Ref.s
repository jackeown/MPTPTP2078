%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 259 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 ( 661 expanded)
%              Number of equality atoms :   37 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f929,f943,f944,f945,f1014,f1096,f1101])).

fof(f1101,plain,
    ( ~ spl6_9
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1097])).

fof(f1097,plain,
    ( $false
    | ~ spl6_9
    | spl6_27 ),
    inference(resolution,[],[f991,f949])).

fof(f949,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f274,f133])).

fof(f133,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f274,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_9
  <=> ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f991,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f990])).

fof(f990,plain,
    ( spl6_27
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1096,plain,(
    spl6_31 ),
    inference(avatar_contradiction_clause,[],[f1092])).

fof(f1092,plain,
    ( $false
    | spl6_31 ),
    inference(resolution,[],[f1060,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f27])).

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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1060,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_31 ),
    inference(trivial_inequality_removal,[],[f1055])).

fof(f1055,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK2,sK1)
    | spl6_31 ),
    inference(superposition,[],[f1013,f89])).

fof(f89,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f1013,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1011,plain,
    ( spl6_31
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1014,plain,
    ( ~ spl6_27
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f702,f1011,f990])).

fof(f702,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f156,f168])).

fof(f168,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f161,f59])).

fof(f59,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f161,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X7,X6)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f45,f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f156,plain,(
    ! [X24,X23,X22] :
      ( r1_xboole_0(X22,k3_tarski(k2_enumset1(X23,X23,X23,X24)))
      | k1_xboole_0 != k3_xboole_0(X22,X24)
      | ~ r1_xboole_0(X22,X23) ) ),
    inference(superposition,[],[f52,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f945,plain,
    ( ~ spl6_11
    | spl6_23 ),
    inference(avatar_split_clause,[],[f889,f931,f346])).

fof(f346,plain,
    ( spl6_11
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f931,plain,
    ( spl6_23
  <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f889,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f199,f60])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f34,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f199,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X16,X15)
      | r1_xboole_0(X15,X16)
      | k1_xboole_0 != X16 ) ),
    inference(superposition,[],[f52,f71])).

fof(f71,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f944,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f296,f276,f346])).

fof(f276,plain,
    ( spl6_10
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f296,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f88,f60])).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f51,f50])).

fof(f943,plain,
    ( spl6_9
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f545,f931,f273])).

fof(f545,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f163,f60])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_xboole_0(X4,X3)
      | ~ r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f65,f50])).

fof(f929,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | spl6_10 ),
    inference(resolution,[],[f913,f36])).

fof(f913,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_10 ),
    inference(resolution,[],[f562,f302])).

fof(f302,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl6_10 ),
    inference(resolution,[],[f287,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f287,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(resolution,[],[f282,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f282,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(resolution,[],[f278,f161])).

fof(f278,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f276])).

fof(f562,plain,(
    ! [X6,X4,X5] :
      ( r1_xboole_0(k3_xboole_0(X6,X5),X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X2,X0) ) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:41 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.46  % (16484)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (16479)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (16488)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (16490)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (16481)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (16482)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (16486)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (16480)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (16493)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (16477)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (16489)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (16478)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (16483)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (16480)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (16487)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (16492)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (16476)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (16491)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1102,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f929,f943,f944,f945,f1014,f1096,f1101])).
% 0.22/0.52  fof(f1101,plain,(
% 0.22/0.52    ~spl6_9 | spl6_27),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1097])).
% 0.22/0.52  fof(f1097,plain,(
% 0.22/0.52    $false | (~spl6_9 | spl6_27)),
% 0.22/0.52    inference(resolution,[],[f991,f949])).
% 0.22/0.52  fof(f949,plain,(
% 0.22/0.52    r1_xboole_0(sK1,sK0) | ~spl6_9),
% 0.22/0.52    inference(resolution,[],[f274,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 0.22/0.52    inference(superposition,[],[f44,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,k3_xboole_0(sK0,sK1))) ) | ~spl6_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f273])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    spl6_9 <=> ! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.52  fof(f991,plain,(
% 0.22/0.52    ~r1_xboole_0(sK1,sK0) | spl6_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f990])).
% 0.22/0.52  fof(f990,plain,(
% 0.22/0.52    spl6_27 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.52  fof(f1096,plain,(
% 0.22/0.52    spl6_31),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1092])).
% 0.22/0.52  fof(f1092,plain,(
% 0.22/0.52    $false | spl6_31),
% 0.22/0.52    inference(resolution,[],[f1060,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    r1_xboole_0(sK2,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f15])).
% 0.22/0.52  fof(f15,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.22/0.52  fof(f1060,plain,(
% 0.22/0.52    ~r1_xboole_0(sK2,sK1) | spl6_31),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1055])).
% 0.22/0.52  fof(f1055,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK2,sK1) | spl6_31),
% 0.22/0.52    inference(superposition,[],[f1013,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) )),
% 0.22/0.52    inference(superposition,[],[f51,f41])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.52  fof(f1013,plain,(
% 0.22/0.52    k1_xboole_0 != k3_xboole_0(sK1,sK2) | spl6_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f1011])).
% 0.22/0.52  fof(f1011,plain,(
% 0.22/0.52    spl6_31 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.52  fof(f1014,plain,(
% 0.22/0.52    ~spl6_27 | ~spl6_31),
% 0.22/0.52    inference(avatar_split_clause,[],[f702,f1011,f990])).
% 0.22/0.52  fof(f702,plain,(
% 0.22/0.52    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f156,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 0.22/0.52    inference(resolution,[],[f161,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.22/0.52    inference(definition_unfolding,[],[f37,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f42,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f43,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X6,X7] : (r1_xboole_0(X7,X6) | ~r1_xboole_0(X6,X7)) )),
% 0.22/0.52    inference(resolution,[],[f65,f44])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(superposition,[],[f45,f41])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X24,X23,X22] : (r1_xboole_0(X22,k3_tarski(k2_enumset1(X23,X23,X23,X24))) | k1_xboole_0 != k3_xboole_0(X22,X24) | ~r1_xboole_0(X22,X23)) )),
% 0.22/0.52    inference(superposition,[],[f52,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f54,f57])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f945,plain,(
% 0.22/0.52    ~spl6_11 | spl6_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f889,f931,f346])).
% 0.22/0.52  fof(f346,plain,(
% 0.22/0.52    spl6_11 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.52  fof(f931,plain,(
% 0.22/0.52    spl6_23 <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.52  fof(f889,plain,(
% 0.22/0.52    r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f199,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.52    inference(definition_unfolding,[],[f34,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f39,f56])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ( ! [X15,X16] : (~r1_tarski(X16,X15) | r1_xboole_0(X15,X16) | k1_xboole_0 != X16) )),
% 0.22/0.52    inference(superposition,[],[f52,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.22/0.52    inference(superposition,[],[f50,f41])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f944,plain,(
% 0.22/0.52    spl6_11 | ~spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f296,f276,f346])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    spl6_10 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f88,f60])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 0.22/0.52    inference(superposition,[],[f51,f50])).
% 0.22/0.52  fof(f943,plain,(
% 0.22/0.52    spl6_9 | ~spl6_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f545,f931,f273])).
% 0.22/0.52  fof(f545,plain,(
% 0.22/0.52    ( ! [X3] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | ~r2_hidden(X3,k3_xboole_0(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f163,f60])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | ~r1_xboole_0(X4,X3) | ~r2_hidden(X5,X3)) )),
% 0.22/0.52    inference(superposition,[],[f65,f50])).
% 0.22/0.52  fof(f929,plain,(
% 0.22/0.52    spl6_10),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f925])).
% 0.22/0.52  fof(f925,plain,(
% 0.22/0.52    $false | spl6_10),
% 0.22/0.52    inference(resolution,[],[f913,f36])).
% 0.22/0.52  fof(f913,plain,(
% 0.22/0.52    ~r1_xboole_0(sK2,sK1) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f562,f302])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f287,f125])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.52    inference(resolution,[],[f48,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    r2_hidden(sK3,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f282,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f49,f58])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f278,f161])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f276])).
% 0.22/0.52  fof(f562,plain,(
% 0.22/0.52    ( ! [X6,X4,X5] : (r1_xboole_0(k3_xboole_0(X6,X5),X4) | ~r1_xboole_0(X4,X5)) )),
% 0.22/0.52    inference(resolution,[],[f180,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.22/0.52    inference(superposition,[],[f40,f41])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f70,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) )),
% 0.22/0.52    inference(resolution,[],[f47,f45])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (16480)------------------------------
% 0.22/0.52  % (16480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16480)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (16480)Memory used [KB]: 6524
% 0.22/0.52  % (16480)Time elapsed: 0.095 s
% 0.22/0.52  % (16480)------------------------------
% 0.22/0.52  % (16480)------------------------------
% 0.22/0.52  % (16475)Success in time 0.153 s
%------------------------------------------------------------------------------
