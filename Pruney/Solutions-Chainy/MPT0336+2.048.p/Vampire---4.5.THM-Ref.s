%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 153 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 367 expanded)
%              Number of equality atoms :   31 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f1044,f1049,f1111,f1117,f1290])).

fof(f1290,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f1286])).

fof(f1286,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f1282,f31])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK1) ),
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

fof(f1282,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_19 ),
    inference(resolution,[],[f1043,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1043,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1041,plain,
    ( spl5_19
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1117,plain,
    ( ~ spl5_7
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f1113])).

fof(f1113,plain,
    ( $false
    | ~ spl5_7
    | spl5_23 ),
    inference(resolution,[],[f1109,f1083])).

fof(f1083,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f1068])).

fof(f1068,plain,
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
    inference(superposition,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
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

fof(f1109,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1107,plain,
    ( spl5_23
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1111,plain,
    ( ~ spl5_19
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f161,f1107,f1041])).

fof(f161,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f59,f60])).

fof(f60,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f1049,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f1038,f33])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1038,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f1036,plain,
    ( spl5_18
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1044,plain,
    ( ~ spl5_19
    | ~ spl5_18
    | spl5_8 ),
    inference(avatar_split_clause,[],[f1033,f176,f1036,f1041])).

fof(f176,plain,
    ( spl5_8
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1033,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_8 ),
    inference(superposition,[],[f822,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f822,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl5_8 ),
    inference(resolution,[],[f642,f198])).

fof(f198,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl5_8 ),
    inference(resolution,[],[f191,f117])).

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

fof(f191,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(resolution,[],[f186,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f186,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(resolution,[],[f178,f43])).

fof(f178,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f642,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(trivial_inequality_removal,[],[f636])).

fof(f636,plain,(
    ! [X23,X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(superposition,[],[f137,f44])).

fof(f137,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14))
      | r1_xboole_0(k3_xboole_0(X12,X13),X14) ) ),
    inference(superposition,[],[f45,f47])).

fof(f47,plain,(
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

fof(f29,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.40  % (980)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.42  % (983)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.44  % (985)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (990)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (987)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (981)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (977)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (979)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (978)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (984)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (975)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (982)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (991)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (986)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (976)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (989)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (988)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (992)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.45/0.54  % (979)Refutation found. Thanks to Tanya!
% 1.45/0.54  % SZS status Theorem for theBenchmark
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  fof(f1291,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f179,f1044,f1049,f1111,f1117,f1290])).
% 1.45/0.54  fof(f1290,plain,(
% 1.45/0.54    spl5_19),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f1286])).
% 1.45/0.54  fof(f1286,plain,(
% 1.45/0.54    $false | spl5_19),
% 1.45/0.54    inference(resolution,[],[f1282,f31])).
% 1.45/0.54  fof(f31,plain,(
% 1.45/0.54    r1_xboole_0(sK2,sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.45/0.54    inference(flattening,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.45/0.54    inference(ennf_transformation,[],[f15])).
% 1.45/0.54  fof(f15,negated_conjecture,(
% 1.45/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.45/0.54    inference(negated_conjecture,[],[f14])).
% 1.45/0.54  fof(f14,conjecture,(
% 1.45/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.45/0.54  fof(f1282,plain,(
% 1.45/0.54    ~r1_xboole_0(sK2,sK1) | spl5_19),
% 1.45/0.54    inference(resolution,[],[f1043,f43])).
% 1.45/0.54  fof(f43,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f3])).
% 1.45/0.54  fof(f3,axiom,(
% 1.45/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.45/0.54  fof(f1043,plain,(
% 1.45/0.54    ~r1_xboole_0(sK1,sK2) | spl5_19),
% 1.45/0.54    inference(avatar_component_clause,[],[f1041])).
% 1.45/0.54  fof(f1041,plain,(
% 1.45/0.54    spl5_19 <=> r1_xboole_0(sK1,sK2)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.45/0.54  fof(f1117,plain,(
% 1.45/0.54    ~spl5_7 | spl5_23),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f1113])).
% 1.45/0.54  fof(f1113,plain,(
% 1.45/0.54    $false | (~spl5_7 | spl5_23)),
% 1.45/0.54    inference(resolution,[],[f1109,f1083])).
% 1.45/0.54  fof(f1083,plain,(
% 1.45/0.54    r1_xboole_0(sK1,sK0) | ~spl5_7),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f1068])).
% 1.45/0.54  fof(f1068,plain,(
% 1.45/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl5_7),
% 1.45/0.54    inference(superposition,[],[f96,f174])).
% 1.45/0.54  fof(f174,plain,(
% 1.45/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_7),
% 1.45/0.54    inference(avatar_component_clause,[],[f172])).
% 1.45/0.54  fof(f172,plain,(
% 1.45/0.54    spl5_7 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.45/0.54  fof(f96,plain,(
% 1.45/0.54    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) )),
% 1.45/0.54    inference(superposition,[],[f45,f35])).
% 1.45/0.54  fof(f35,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.45/0.54    inference(nnf_transformation,[],[f2])).
% 1.45/0.54  fof(f2,axiom,(
% 1.45/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.45/0.54  fof(f1109,plain,(
% 1.45/0.54    ~r1_xboole_0(sK1,sK0) | spl5_23),
% 1.45/0.54    inference(avatar_component_clause,[],[f1107])).
% 1.45/0.54  fof(f1107,plain,(
% 1.45/0.54    spl5_23 <=> r1_xboole_0(sK1,sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.45/0.54  fof(f1111,plain,(
% 1.45/0.54    ~spl5_19 | ~spl5_23),
% 1.45/0.54    inference(avatar_split_clause,[],[f161,f1107,f1041])).
% 1.45/0.54  fof(f161,plain,(
% 1.45/0.54    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.45/0.54    inference(resolution,[],[f59,f60])).
% 1.45/0.54  fof(f60,plain,(
% 1.45/0.54    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 1.45/0.54    inference(resolution,[],[f54,f43])).
% 1.45/0.54  fof(f54,plain,(
% 1.45/0.54    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 1.45/0.54    inference(definition_unfolding,[],[f32,f52])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.45/0.54    inference(definition_unfolding,[],[f36,f51])).
% 1.45/0.54  fof(f51,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f37,f46])).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.54  fof(f37,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f10])).
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f13])).
% 1.45/0.54  fof(f13,axiom,(
% 1.45/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f59,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f48,f52])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.45/0.54  fof(f1049,plain,(
% 1.45/0.54    spl5_18),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f1045])).
% 1.45/0.54  fof(f1045,plain,(
% 1.45/0.54    $false | spl5_18),
% 1.45/0.54    inference(resolution,[],[f1038,f33])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f7])).
% 1.45/0.54  fof(f7,axiom,(
% 1.45/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.45/0.54  fof(f1038,plain,(
% 1.45/0.54    ~r1_xboole_0(sK0,k1_xboole_0) | spl5_18),
% 1.45/0.54    inference(avatar_component_clause,[],[f1036])).
% 1.45/0.54  fof(f1036,plain,(
% 1.45/0.54    spl5_18 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.45/0.54  fof(f1044,plain,(
% 1.45/0.54    ~spl5_19 | ~spl5_18 | spl5_8),
% 1.45/0.54    inference(avatar_split_clause,[],[f1033,f176,f1036,f1041])).
% 1.45/0.54  fof(f176,plain,(
% 1.45/0.54    spl5_8 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.45/0.54  fof(f1033,plain,(
% 1.45/0.54    ~r1_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK1,sK2) | spl5_8),
% 1.45/0.54    inference(superposition,[],[f822,f44])).
% 1.45/0.54  fof(f44,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f822,plain,(
% 1.45/0.54    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl5_8),
% 1.45/0.54    inference(resolution,[],[f642,f198])).
% 1.45/0.54  fof(f198,plain,(
% 1.45/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl5_8),
% 1.45/0.54    inference(resolution,[],[f191,f117])).
% 1.45/0.54  fof(f117,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.45/0.54    inference(resolution,[],[f40,f30])).
% 1.45/0.54  fof(f30,plain,(
% 1.45/0.54    r2_hidden(sK3,sK2)),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f16])).
% 1.45/0.54  fof(f16,plain,(
% 1.45/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.54    inference(rectify,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.54  fof(f191,plain,(
% 1.45/0.54    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl5_8),
% 1.45/0.54    inference(resolution,[],[f186,f56])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f41,f53])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f34,f51])).
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.54  fof(f41,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,axiom,(
% 1.45/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.45/0.54  fof(f186,plain,(
% 1.45/0.54    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl5_8),
% 1.45/0.54    inference(resolution,[],[f178,f43])).
% 1.45/0.54  fof(f178,plain,(
% 1.45/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_8),
% 1.45/0.54    inference(avatar_component_clause,[],[f176])).
% 1.45/0.54  fof(f642,plain,(
% 1.45/0.54    ( ! [X23,X21,X22] : (r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f636])).
% 1.45/0.54  fof(f636,plain,(
% 1.45/0.54    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 1.45/0.54    inference(superposition,[],[f137,f44])).
% 1.45/0.54  fof(f137,plain,(
% 1.45/0.54    ( ! [X14,X12,X13] : (k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14)) | r1_xboole_0(k3_xboole_0(X12,X13),X14)) )),
% 1.45/0.54    inference(superposition,[],[f45,f47])).
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.45/0.54  fof(f179,plain,(
% 1.45/0.54    spl5_7 | ~spl5_8),
% 1.45/0.54    inference(avatar_split_clause,[],[f170,f176,f172])).
% 1.45/0.54  fof(f170,plain,(
% 1.45/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.45/0.54    inference(resolution,[],[f76,f55])).
% 1.45/0.54  fof(f55,plain,(
% 1.45/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.45/0.54    inference(definition_unfolding,[],[f29,f53])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 1.45/0.54    inference(superposition,[],[f44,f42])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (979)------------------------------
% 1.45/0.54  % (979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (979)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (979)Memory used [KB]: 6908
% 1.45/0.54  % (979)Time elapsed: 0.122 s
% 1.45/0.54  % (979)------------------------------
% 1.45/0.54  % (979)------------------------------
% 1.45/0.54  % (974)Success in time 0.199 s
%------------------------------------------------------------------------------
