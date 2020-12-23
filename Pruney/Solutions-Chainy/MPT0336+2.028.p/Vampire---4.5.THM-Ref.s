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
% DateTime   : Thu Dec  3 12:43:27 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 170 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 ( 478 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1526,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f571,f787,f1525])).

fof(f1525,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1524])).

fof(f1524,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1523,f240])).

fof(f240,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f63,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25])).

fof(f25,plain,
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f232,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f117,f35])).

fof(f35,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f52,f45])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
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

fof(f1523,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f1516,f45])).

fof(f1516,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f1453,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(extensionality_resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1453,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f128,f684])).

fof(f684,plain,
    ( ! [X2] : k4_xboole_0(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X2
    | ~ spl5_7 ),
    inference(resolution,[],[f566,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f566,plain,
    ( ! [X14] : r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl5_7
  <=> ! [X14] : r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f128,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f37,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f787,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f784,f63])).

fof(f784,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f586,f132])).

fof(f132,plain,(
    ! [X10,X8,X9] :
      ( r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X10)
      | ~ r1_xboole_0(X8,X10) ) ),
    inference(superposition,[],[f94,f59])).

fof(f94,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k4_xboole_0(X2,X4),X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f586,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f570,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).

fof(f27,plain,(
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

fof(f570,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl5_8
  <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f571,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f562,f568,f565])).

fof(f562,plain,(
    ! [X14] :
      ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
      | r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f168,f219])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X6,X5),X4)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X6,X5) ) ),
    inference(resolution,[],[f43,f42])).

fof(f168,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f95,plain,(
    ! [X5] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X5)
      | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5) ) ),
    inference(resolution,[],[f55,f58])).

fof(f58,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f32,f40,f57])).

fof(f32,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:54:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (1571)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (1562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (1555)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (1551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (1554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (1556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (1552)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (1548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (1575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (1549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (1576)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (1574)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (1568)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (1563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.56  % (1570)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.56  % (1567)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.56  % (1578)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.56  % (1553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.56  % (1566)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.56  % (1559)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.56  % (1572)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.56  % (1557)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.56  % (1573)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.56  % (1558)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.57  % (1565)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.57  % (1561)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (1560)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.59  % (1569)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.59  % (1577)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.60  % (1554)Refutation found. Thanks to Tanya!
% 1.56/0.60  % SZS status Theorem for theBenchmark
% 1.56/0.60  % SZS output start Proof for theBenchmark
% 1.56/0.60  fof(f1526,plain,(
% 1.56/0.60    $false),
% 1.56/0.60    inference(avatar_sat_refutation,[],[f571,f787,f1525])).
% 1.56/0.60  fof(f1525,plain,(
% 1.56/0.60    ~spl5_7),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f1524])).
% 1.56/0.60  fof(f1524,plain,(
% 1.56/0.60    $false | ~spl5_7),
% 1.56/0.60    inference(subsumption_resolution,[],[f1523,f240])).
% 1.56/0.60  fof(f240,plain,(
% 1.56/0.60    ~r1_xboole_0(sK1,sK0)),
% 1.56/0.60    inference(subsumption_resolution,[],[f232,f63])).
% 1.56/0.60  fof(f63,plain,(
% 1.56/0.60    r1_xboole_0(sK1,sK2)),
% 1.56/0.60    inference(resolution,[],[f45,f34])).
% 1.56/0.60  fof(f34,plain,(
% 1.56/0.60    r1_xboole_0(sK2,sK1)),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  fof(f26,plain,(
% 1.56/0.60    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25])).
% 1.56/0.60  fof(f25,plain,(
% 1.56/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f18,plain,(
% 1.56/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.56/0.60    inference(flattening,[],[f17])).
% 1.56/0.60  fof(f17,plain,(
% 1.56/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.56/0.60    inference(ennf_transformation,[],[f15])).
% 1.56/0.60  fof(f15,negated_conjecture,(
% 1.56/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.56/0.60    inference(negated_conjecture,[],[f14])).
% 1.56/0.60  fof(f14,conjecture,(
% 1.56/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.56/0.60  fof(f45,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f21])).
% 1.56/0.60  fof(f21,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f2])).
% 1.56/0.60  fof(f2,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.56/0.60  fof(f232,plain,(
% 1.56/0.60    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.56/0.60    inference(resolution,[],[f117,f35])).
% 1.56/0.60  fof(f35,plain,(
% 1.56/0.60    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  fof(f117,plain,(
% 1.56/0.60    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 1.56/0.60    inference(resolution,[],[f52,f45])).
% 1.56/0.60  fof(f52,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f22])).
% 1.56/0.60  fof(f22,plain,(
% 1.56/0.60    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.60    inference(ennf_transformation,[],[f8])).
% 1.56/0.60  fof(f8,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.56/0.60  fof(f1523,plain,(
% 1.56/0.60    r1_xboole_0(sK1,sK0) | ~spl5_7),
% 1.56/0.60    inference(resolution,[],[f1516,f45])).
% 1.56/0.60  fof(f1516,plain,(
% 1.56/0.60    r1_xboole_0(sK0,sK1) | ~spl5_7),
% 1.56/0.60    inference(resolution,[],[f1453,f82])).
% 1.56/0.60  fof(f82,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.56/0.60    inference(subsumption_resolution,[],[f77,f37])).
% 1.56/0.60  fof(f37,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f5])).
% 1.56/0.60  fof(f5,axiom,(
% 1.56/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.56/0.60  fof(f77,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X0,X1)) | ~r1_tarski(k4_xboole_0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.56/0.60    inference(extensionality_resolution,[],[f48,f50])).
% 1.56/0.60  fof(f50,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f31])).
% 1.56/0.60  fof(f31,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.60    inference(nnf_transformation,[],[f9])).
% 1.56/0.60  fof(f9,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.56/0.60  fof(f48,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f30,plain,(
% 1.56/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.60    inference(flattening,[],[f29])).
% 1.56/0.60  fof(f29,plain,(
% 1.56/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.60    inference(nnf_transformation,[],[f4])).
% 1.56/0.60  fof(f4,axiom,(
% 1.56/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.60  fof(f1453,plain,(
% 1.56/0.60    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.56/0.60    inference(superposition,[],[f128,f684])).
% 1.56/0.60  fof(f684,plain,(
% 1.56/0.60    ( ! [X2] : (k4_xboole_0(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X2) ) | ~spl5_7),
% 1.56/0.60    inference(resolution,[],[f566,f49])).
% 1.56/0.60  fof(f49,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.56/0.60    inference(cnf_transformation,[],[f31])).
% 1.56/0.60  fof(f566,plain,(
% 1.56/0.60    ( ! [X14] : (r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_7),
% 1.56/0.60    inference(avatar_component_clause,[],[f565])).
% 1.56/0.60  fof(f565,plain,(
% 1.56/0.60    spl5_7 <=> ! [X14] : r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.56/0.60  fof(f128,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 1.56/0.60    inference(superposition,[],[f37,f59])).
% 1.56/0.60  fof(f59,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.56/0.60    inference(definition_unfolding,[],[f38,f40,f40])).
% 1.56/0.60  fof(f40,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f6])).
% 1.56/0.60  fof(f6,axiom,(
% 1.56/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.56/0.60  fof(f38,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f1])).
% 1.56/0.60  fof(f1,axiom,(
% 1.56/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.60  fof(f787,plain,(
% 1.56/0.60    ~spl5_8),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f786])).
% 1.56/0.60  fof(f786,plain,(
% 1.56/0.60    $false | ~spl5_8),
% 1.56/0.60    inference(subsumption_resolution,[],[f784,f63])).
% 1.56/0.60  fof(f784,plain,(
% 1.56/0.60    ~r1_xboole_0(sK1,sK2) | ~spl5_8),
% 1.56/0.60    inference(resolution,[],[f586,f132])).
% 1.56/0.60  fof(f132,plain,(
% 1.56/0.60    ( ! [X10,X8,X9] : (r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X10) | ~r1_xboole_0(X8,X10)) )),
% 1.56/0.60    inference(superposition,[],[f94,f59])).
% 1.56/0.60  fof(f94,plain,(
% 1.56/0.60    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,X4),X3) | ~r1_xboole_0(X2,X3)) )),
% 1.56/0.60    inference(resolution,[],[f55,f37])).
% 1.56/0.60  fof(f55,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f24])).
% 1.56/0.60  fof(f24,plain,(
% 1.56/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.60    inference(flattening,[],[f23])).
% 1.56/0.60  fof(f23,plain,(
% 1.56/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(ennf_transformation,[],[f7])).
% 1.56/0.60  fof(f7,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.56/0.60  fof(f586,plain,(
% 1.56/0.60    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl5_8),
% 1.56/0.60    inference(resolution,[],[f570,f73])).
% 1.56/0.60  fof(f73,plain,(
% 1.56/0.60    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.56/0.60    inference(resolution,[],[f43,f33])).
% 1.56/0.60  fof(f33,plain,(
% 1.56/0.60    r2_hidden(sK3,sK2)),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  fof(f43,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f28])).
% 1.56/0.60  fof(f28,plain,(
% 1.56/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).
% 1.56/0.60  fof(f27,plain,(
% 1.56/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f19,plain,(
% 1.56/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.56/0.60    inference(ennf_transformation,[],[f16])).
% 1.56/0.60  fof(f16,plain,(
% 1.56/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.60    inference(rectify,[],[f3])).
% 1.56/0.60  fof(f3,axiom,(
% 1.56/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.56/0.60  fof(f570,plain,(
% 1.56/0.60    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl5_8),
% 1.56/0.60    inference(avatar_component_clause,[],[f568])).
% 1.56/0.60  fof(f568,plain,(
% 1.56/0.60    spl5_8 <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.56/0.60  fof(f571,plain,(
% 1.56/0.60    spl5_7 | spl5_8),
% 1.56/0.60    inference(avatar_split_clause,[],[f562,f568,f565])).
% 1.56/0.60  fof(f562,plain,(
% 1.56/0.60    ( ! [X14] : (r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | r1_xboole_0(X14,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 1.56/0.60    inference(resolution,[],[f168,f219])).
% 1.56/0.60  fof(f219,plain,(
% 1.56/0.60    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)) )),
% 1.56/0.60    inference(duplicate_literal_removal,[],[f218])).
% 1.56/0.60  fof(f218,plain,(
% 1.56/0.60    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.56/0.60    inference(resolution,[],[f75,f42])).
% 1.56/0.60  fof(f42,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f28])).
% 1.56/0.60  fof(f75,plain,(
% 1.56/0.60    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X6,X5),X4) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X6,X5)) )),
% 1.56/0.60    inference(resolution,[],[f43,f42])).
% 1.56/0.60  fof(f168,plain,(
% 1.56/0.60    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | r2_hidden(sK3,X0)) )),
% 1.56/0.60    inference(resolution,[],[f95,f60])).
% 1.56/0.60  fof(f60,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.56/0.60    inference(definition_unfolding,[],[f44,f57])).
% 1.56/0.60  fof(f57,plain,(
% 1.56/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.60    inference(definition_unfolding,[],[f36,f56])).
% 1.56/0.60  fof(f56,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.60    inference(definition_unfolding,[],[f39,f51])).
% 1.56/0.60  fof(f51,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f12])).
% 1.56/0.60  fof(f12,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.60  fof(f39,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f11])).
% 1.56/0.60  fof(f11,axiom,(
% 1.56/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.60  fof(f36,plain,(
% 1.56/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f10])).
% 1.56/0.60  fof(f10,axiom,(
% 1.56/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.60  fof(f44,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f20])).
% 1.56/0.60  fof(f20,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f13])).
% 1.56/0.60  fof(f13,axiom,(
% 1.56/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.56/0.60  fof(f95,plain,(
% 1.56/0.60    ( ! [X5] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X5) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5)) )),
% 1.56/0.60    inference(resolution,[],[f55,f58])).
% 1.56/0.60  fof(f58,plain,(
% 1.56/0.60    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.56/0.60    inference(definition_unfolding,[],[f32,f40,f57])).
% 1.56/0.60  fof(f32,plain,(
% 1.56/0.60    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  % SZS output end Proof for theBenchmark
% 1.56/0.60  % (1554)------------------------------
% 1.56/0.60  % (1554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (1554)Termination reason: Refutation
% 1.56/0.60  
% 1.56/0.60  % (1554)Memory used [KB]: 11513
% 1.56/0.60  % (1554)Time elapsed: 0.121 s
% 1.56/0.60  % (1554)------------------------------
% 1.56/0.60  % (1554)------------------------------
% 1.56/0.60  % (1546)Success in time 0.234 s
%------------------------------------------------------------------------------
