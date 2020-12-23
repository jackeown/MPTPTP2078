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
% DateTime   : Thu Dec  3 12:43:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 151 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 371 expanded)
%              Number of equality atoms :   31 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f909,f1054,f1124,f1294,f1295])).

fof(f1295,plain,
    ( ~ spl5_19
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f161,f1115,f906])).

fof(f906,plain,
    ( spl5_19
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1115,plain,
    ( spl5_23
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f161,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f54,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).

fof(f24,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f1294,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f1290])).

fof(f1290,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f1064,f31])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f1064,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_19 ),
    inference(resolution,[],[f908,f42])).

fof(f908,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f906])).

fof(f1124,plain,
    ( ~ spl5_7
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl5_7
    | spl5_23 ),
    inference(resolution,[],[f1117,f1091])).

fof(f1091,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f1076])).

fof(f1076,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(superposition,[],[f96,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_7
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f96,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k3_xboole_0(X5,X4)
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f1117,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f1054,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1050])).

fof(f1050,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f903,f33])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f903,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f901])).

fof(f901,plain,
    ( spl5_18
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f909,plain,
    ( ~ spl5_19
    | ~ spl5_18
    | spl5_8 ),
    inference(avatar_split_clause,[],[f898,f176,f901,f906])).

fof(f176,plain,
    ( spl5_8
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f898,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_8 ),
    inference(superposition,[],[f827,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f827,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl5_8 ),
    inference(resolution,[],[f646,f199])).

fof(f199,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl5_8 ),
    inference(resolution,[],[f197,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f197,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(resolution,[],[f186,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f186,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(resolution,[],[f178,f42])).

fof(f178,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f646,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(trivial_inequality_removal,[],[f640])).

fof(f640,plain,(
    ! [X23,X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(superposition,[],[f136,f43])).

fof(f136,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14))
      | r1_xboole_0(k3_xboole_0(X12,X13),X14) ) ),
    inference(superposition,[],[f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f179,plain,
    ( spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f170,f176,f172])).

fof(f170,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f29,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:37:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.43  % (30423)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (30426)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (30414)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (30425)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (30415)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (30412)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (30418)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (30417)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30416)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (30421)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (30420)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (30422)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (30427)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (30419)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (30413)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (30429)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (30424)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (30428)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.56  % (30416)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1296,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f179,f909,f1054,f1124,f1294,f1295])).
% 0.21/0.56  fof(f1295,plain,(
% 0.21/0.56    ~spl5_19 | ~spl5_23),
% 0.21/0.56    inference(avatar_split_clause,[],[f161,f1115,f906])).
% 0.21/0.56  fof(f906,plain,(
% 0.21/0.56    spl5_19 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.56  fof(f1115,plain,(
% 0.21/0.56    spl5_23 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(resolution,[],[f58,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 0.21/0.56    inference(resolution,[],[f54,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.21/0.56    inference(definition_unfolding,[],[f32,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f36,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f37,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f14])).
% 0.21/0.56  fof(f14,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f52])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.56  fof(f1294,plain,(
% 0.21/0.56    spl5_19),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1290])).
% 0.21/0.56  fof(f1290,plain,(
% 0.21/0.56    $false | spl5_19),
% 0.21/0.56    inference(resolution,[],[f1064,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    r1_xboole_0(sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f1064,plain,(
% 0.21/0.56    ~r1_xboole_0(sK2,sK1) | spl5_19),
% 0.21/0.56    inference(resolution,[],[f908,f42])).
% 0.21/0.56  fof(f908,plain,(
% 0.21/0.56    ~r1_xboole_0(sK1,sK2) | spl5_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f906])).
% 0.21/0.56  fof(f1124,plain,(
% 0.21/0.56    ~spl5_7 | spl5_23),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1120])).
% 0.21/0.56  fof(f1120,plain,(
% 0.21/0.56    $false | (~spl5_7 | spl5_23)),
% 0.21/0.56    inference(resolution,[],[f1117,f1091])).
% 0.21/0.56  fof(f1091,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK0) | ~spl5_7),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f1076])).
% 0.21/0.56  fof(f1076,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl5_7),
% 0.21/0.56    inference(superposition,[],[f96,f174])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    spl5_7 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) )),
% 0.21/0.56    inference(superposition,[],[f44,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.56  fof(f1117,plain,(
% 0.21/0.56    ~r1_xboole_0(sK1,sK0) | spl5_23),
% 0.21/0.56    inference(avatar_component_clause,[],[f1115])).
% 0.21/0.56  fof(f1054,plain,(
% 0.21/0.56    spl5_18),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1050])).
% 0.21/0.56  fof(f1050,plain,(
% 0.21/0.56    $false | spl5_18),
% 0.21/0.56    inference(resolution,[],[f903,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.56  fof(f903,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,k1_xboole_0) | spl5_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f901])).
% 0.21/0.56  fof(f901,plain,(
% 0.21/0.56    spl5_18 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.56  fof(f909,plain,(
% 0.21/0.56    ~spl5_19 | ~spl5_18 | spl5_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f898,f176,f901,f906])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    spl5_8 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.56  fof(f898,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK1,sK2) | spl5_8),
% 0.21/0.56    inference(superposition,[],[f827,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f827,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl5_8),
% 0.21/0.56    inference(resolution,[],[f646,f199])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl5_8),
% 0.21/0.56    inference(resolution,[],[f197,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f40,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    r2_hidden(sK3,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl5_8),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.57    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl5_8),
% 0.21/0.57    inference(resolution,[],[f186,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f51])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl5_8),
% 0.21/0.57    inference(resolution,[],[f178,f42])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f176])).
% 0.21/0.57  fof(f646,plain,(
% 0.21/0.57    ( ! [X23,X21,X22] : (r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f640])).
% 0.21/0.57  fof(f640,plain,(
% 0.21/0.57    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 0.21/0.57    inference(superposition,[],[f136,f43])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ( ! [X14,X12,X13] : (k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14)) | r1_xboole_0(k3_xboole_0(X12,X13),X14)) )),
% 0.21/0.57    inference(superposition,[],[f44,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.57  fof(f179,plain,(
% 0.21/0.57    spl5_7 | ~spl5_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f170,f176,f172])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f76,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f51])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 0.21/0.57    inference(superposition,[],[f43,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (30416)------------------------------
% 0.21/0.57  % (30416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30416)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (30416)Memory used [KB]: 6908
% 0.21/0.57  % (30416)Time elapsed: 0.143 s
% 0.21/0.57  % (30416)------------------------------
% 0.21/0.57  % (30416)------------------------------
% 0.21/0.57  % (30411)Success in time 0.203 s
%------------------------------------------------------------------------------
