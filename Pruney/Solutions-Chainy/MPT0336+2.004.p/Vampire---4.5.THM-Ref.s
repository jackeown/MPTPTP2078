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
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   23
%              Number of atoms          :  320 ( 516 expanded)
%              Number of equality atoms :  158 ( 202 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1320,plain,(
    $false ),
    inference(resolution,[],[f1318,f45])).

fof(f45,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1318,plain,(
    r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(resolution,[],[f1289,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1289,plain,(
    r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f1286])).

fof(f1286,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f74,f1147])).

fof(f1147,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f1141,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1141,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,sK1)) ),
    inference(trivial_inequality_removal,[],[f1136])).

fof(f1136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f469,f1108])).

fof(f1108,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1091,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1091,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1086,f48])).

fof(f1086,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f1083])).

fof(f1083,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f74,f1072])).

fof(f1072,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f564,f179])).

fof(f179,plain,(
    ! [X1] : r1_xboole_0(sK3,k3_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f158,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f158,plain,(
    ! [X1] : r1_xboole_0(sK3,k3_xboole_0(sK2,X1)) ),
    inference(resolution,[],[f134,f48])).

fof(f134,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(sK2,X0),sK3) ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK3) ) ),
    inference(resolution,[],[f113,f75])).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK3) ) ),
    inference(superposition,[],[f60,f101])).

fof(f101,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f44,f73])).

fof(f44,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f564,plain,
    ( ~ r1_xboole_0(sK3,k3_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f227,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r1_xboole_0(sK3,X0) ) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f43,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f227,plain,
    ( r2_hidden(sK4,k3_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f143,f89])).

fof(f89,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f143,plain,
    ( sP0(sK4,sK4,k3_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f90,f116])).

fof(f116,plain,
    ( k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_enumset1(X0,X0,X2) = X3
      | k1_enumset1(X1,X1,X2) = X3
      | k1_enumset1(X0,X0,X1) = X3
      | k1_enumset1(X2,X2,X2) = X3
      | k1_enumset1(X1,X1,X1) = X3
      | k1_enumset1(X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f62,f76,f76,f76,f77,f77,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f78,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_enumset1(sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f42,f77])).

fof(f42,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f12,f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f469,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_xboole_0(sK2,X0)
      | k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) ) ),
    inference(resolution,[],[f129,f73])).

fof(f129,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2,k2_xboole_0(sK3,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,X0) ) ),
    inference(superposition,[],[f74,f106])).

fof(f106,plain,(
    ! [X0] : k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,X0) ),
    inference(resolution,[],[f102,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f102,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f44,f48])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14860)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.49  % (14876)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (14850)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (14853)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.52  % (14858)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.25/0.52  % (14868)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.53  % (14859)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.25/0.53  % (14848)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (14870)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.53  % (14865)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.53  % (14849)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.54  % (14862)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.54  % (14867)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.25/0.54  % (14877)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.25/0.54  % (14877)Refutation not found, incomplete strategy% (14877)------------------------------
% 1.25/0.54  % (14877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (14877)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (14877)Memory used [KB]: 1791
% 1.25/0.54  % (14877)Time elapsed: 0.128 s
% 1.25/0.54  % (14877)------------------------------
% 1.25/0.54  % (14877)------------------------------
% 1.25/0.54  % (14851)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.54  % (14873)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.54  % (14854)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (14852)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.37/0.55  % (14864)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.55  % (14869)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (14864)Refutation not found, incomplete strategy% (14864)------------------------------
% 1.37/0.55  % (14864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (14864)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (14864)Memory used [KB]: 10618
% 1.37/0.55  % (14864)Time elapsed: 0.137 s
% 1.37/0.55  % (14864)------------------------------
% 1.37/0.55  % (14864)------------------------------
% 1.37/0.55  % (14857)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (14856)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.55  % (14861)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.55  % (14863)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.56  % (14875)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.56  % (14872)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.56  % (14874)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.56  % (14866)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.56  % (14855)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.57  % (14871)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.59  % (14849)Refutation found. Thanks to Tanya!
% 1.37/0.59  % SZS status Theorem for theBenchmark
% 1.37/0.59  % SZS output start Proof for theBenchmark
% 1.37/0.59  fof(f1320,plain,(
% 1.37/0.59    $false),
% 1.37/0.59    inference(resolution,[],[f1318,f45])).
% 1.37/0.59  fof(f45,plain,(
% 1.37/0.59    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 1.37/0.59    inference(cnf_transformation,[],[f30])).
% 1.37/0.59  fof(f30,plain,(
% 1.37/0.59    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 1.37/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29])).
% 1.37/0.59  fof(f29,plain,(
% 1.37/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 1.37/0.59    introduced(choice_axiom,[])).
% 1.37/0.59  fof(f21,plain,(
% 1.37/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.37/0.59    inference(flattening,[],[f20])).
% 1.37/0.59  fof(f20,plain,(
% 1.37/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.37/0.59    inference(ennf_transformation,[],[f18])).
% 1.37/0.59  fof(f18,negated_conjecture,(
% 1.37/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.37/0.59    inference(negated_conjecture,[],[f17])).
% 1.37/0.59  fof(f17,conjecture,(
% 1.37/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.37/0.59  fof(f1318,plain,(
% 1.37/0.59    r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 1.37/0.59    inference(resolution,[],[f1289,f48])).
% 1.37/0.59  fof(f48,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f23])).
% 1.37/0.59  fof(f23,plain,(
% 1.37/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.37/0.59    inference(ennf_transformation,[],[f4])).
% 1.37/0.59  fof(f4,axiom,(
% 1.37/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.37/0.59  fof(f1289,plain,(
% 1.37/0.59    r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 1.37/0.59    inference(trivial_inequality_removal,[],[f1286])).
% 1.37/0.59  fof(f1286,plain,(
% 1.37/0.59    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 1.37/0.59    inference(superposition,[],[f74,f1147])).
% 1.37/0.59  fof(f1147,plain,(
% 1.37/0.59    k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 1.37/0.59    inference(forward_demodulation,[],[f1141,f47])).
% 1.37/0.59  fof(f47,plain,(
% 1.37/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f1])).
% 1.37/0.59  fof(f1,axiom,(
% 1.37/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.37/0.59  fof(f1141,plain,(
% 1.37/0.59    k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,sK1))),
% 1.37/0.59    inference(trivial_inequality_removal,[],[f1136])).
% 1.37/0.59  fof(f1136,plain,(
% 1.37/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,sK1))),
% 1.37/0.59    inference(superposition,[],[f469,f1108])).
% 1.37/0.59  fof(f1108,plain,(
% 1.37/0.59    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.37/0.59    inference(resolution,[],[f1091,f73])).
% 1.37/0.59  fof(f73,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.37/0.59    inference(cnf_transformation,[],[f41])).
% 1.37/0.59  fof(f41,plain,(
% 1.37/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.37/0.59    inference(nnf_transformation,[],[f3])).
% 1.37/0.59  fof(f3,axiom,(
% 1.37/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.37/0.59  fof(f1091,plain,(
% 1.37/0.59    r1_xboole_0(sK2,sK1)),
% 1.37/0.59    inference(resolution,[],[f1086,f48])).
% 1.37/0.59  fof(f1086,plain,(
% 1.37/0.59    r1_xboole_0(sK1,sK2)),
% 1.37/0.59    inference(trivial_inequality_removal,[],[f1083])).
% 1.37/0.59  fof(f1083,plain,(
% 1.37/0.59    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK2)),
% 1.37/0.59    inference(superposition,[],[f74,f1072])).
% 1.37/0.59  fof(f1072,plain,(
% 1.37/0.59    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.37/0.59    inference(resolution,[],[f564,f179])).
% 1.37/0.59  fof(f179,plain,(
% 1.37/0.59    ( ! [X1] : (r1_xboole_0(sK3,k3_xboole_0(X1,sK2))) )),
% 1.37/0.59    inference(superposition,[],[f158,f72])).
% 1.37/0.59  fof(f72,plain,(
% 1.37/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f2])).
% 1.37/0.59  fof(f2,axiom,(
% 1.37/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.37/0.59  fof(f158,plain,(
% 1.37/0.59    ( ! [X1] : (r1_xboole_0(sK3,k3_xboole_0(sK2,X1))) )),
% 1.37/0.59    inference(resolution,[],[f134,f48])).
% 1.37/0.59  fof(f134,plain,(
% 1.37/0.59    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK2,X0),sK3)) )),
% 1.37/0.59    inference(resolution,[],[f133,f61])).
% 1.37/0.59  fof(f61,plain,(
% 1.37/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f7])).
% 1.37/0.59  fof(f7,axiom,(
% 1.37/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.37/0.59  fof(f133,plain,(
% 1.37/0.59    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK3)) )),
% 1.37/0.59    inference(resolution,[],[f113,f75])).
% 1.37/0.59  fof(f75,plain,(
% 1.37/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f8])).
% 1.37/0.59  fof(f8,axiom,(
% 1.37/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.37/0.59  fof(f113,plain,(
% 1.37/0.59    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK3)) )),
% 1.37/0.59    inference(superposition,[],[f60,f101])).
% 1.37/0.59  fof(f101,plain,(
% 1.37/0.59    k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 1.37/0.59    inference(resolution,[],[f44,f73])).
% 1.37/0.59  fof(f44,plain,(
% 1.37/0.59    r1_xboole_0(sK3,sK2)),
% 1.37/0.59    inference(cnf_transformation,[],[f30])).
% 1.37/0.59  fof(f60,plain,(
% 1.37/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f25])).
% 1.37/0.59  fof(f25,plain,(
% 1.37/0.59    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 1.37/0.59    inference(ennf_transformation,[],[f9])).
% 1.37/0.59  fof(f9,axiom,(
% 1.37/0.59    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.37/0.59  fof(f564,plain,(
% 1.37/0.59    ~r1_xboole_0(sK3,k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.37/0.59    inference(resolution,[],[f227,f99])).
% 1.37/0.59  fof(f99,plain,(
% 1.37/0.59    ( ! [X0] : (~r2_hidden(sK4,X0) | ~r1_xboole_0(sK3,X0)) )),
% 1.37/0.59    inference(resolution,[],[f43,f59])).
% 1.37/0.59  fof(f59,plain,(
% 1.37/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f38])).
% 1.37/0.59  fof(f38,plain,(
% 1.37/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.37/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f37])).
% 1.37/0.59  fof(f37,plain,(
% 1.37/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.37/0.59    introduced(choice_axiom,[])).
% 1.37/0.59  fof(f24,plain,(
% 1.37/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.37/0.59    inference(ennf_transformation,[],[f19])).
% 1.37/0.59  fof(f19,plain,(
% 1.37/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.59    inference(rectify,[],[f5])).
% 1.37/0.59  fof(f5,axiom,(
% 1.37/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.37/0.59  fof(f43,plain,(
% 1.37/0.59    r2_hidden(sK4,sK3)),
% 1.37/0.59    inference(cnf_transformation,[],[f30])).
% 1.37/0.59  fof(f227,plain,(
% 1.37/0.59    r2_hidden(sK4,k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.37/0.59    inference(resolution,[],[f143,f89])).
% 1.37/0.59  fof(f89,plain,(
% 1.37/0.59    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.37/0.59    inference(equality_resolution,[],[f50])).
% 1.37/0.59  fof(f50,plain,(
% 1.37/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f35])).
% 1.37/0.59  fof(f35,plain,(
% 1.37/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.37/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.37/0.59  fof(f34,plain,(
% 1.37/0.59    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.37/0.59    introduced(choice_axiom,[])).
% 1.37/0.59  fof(f33,plain,(
% 1.37/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.37/0.59    inference(rectify,[],[f32])).
% 1.37/0.60  fof(f32,plain,(
% 1.37/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.37/0.60    inference(flattening,[],[f31])).
% 1.37/0.60  fof(f31,plain,(
% 1.37/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.37/0.60    inference(nnf_transformation,[],[f27])).
% 1.37/0.60  fof(f27,plain,(
% 1.37/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.37/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.37/0.60  fof(f143,plain,(
% 1.37/0.60    sP0(sK4,sK4,k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.37/0.60    inference(superposition,[],[f90,f116])).
% 1.37/0.60  fof(f116,plain,(
% 1.37/0.60    k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.37/0.60    inference(duplicate_literal_removal,[],[f115])).
% 1.37/0.60  fof(f115,plain,(
% 1.37/0.60    k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4) | k1_xboole_0 = k3_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) = k1_enumset1(sK4,sK4,sK4)),
% 1.37/0.60    inference(resolution,[],[f78,f87])).
% 1.37/0.60  fof(f87,plain,(
% 1.37/0.60    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_enumset1(X0,X0,X2) = X3 | k1_enumset1(X1,X1,X2) = X3 | k1_enumset1(X0,X0,X1) = X3 | k1_enumset1(X2,X2,X2) = X3 | k1_enumset1(X1,X1,X1) = X3 | k1_enumset1(X0,X0,X0) = X3 | k1_xboole_0 = X3 | k1_enumset1(X0,X1,X2) = X3) )),
% 1.37/0.60    inference(definition_unfolding,[],[f62,f76,f76,f76,f77,f77,f77])).
% 1.37/0.60  fof(f77,plain,(
% 1.37/0.60    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.37/0.60    inference(definition_unfolding,[],[f71,f76])).
% 1.37/0.60  fof(f71,plain,(
% 1.37/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f13])).
% 1.37/0.60  fof(f13,axiom,(
% 1.37/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.60  fof(f76,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f14])).
% 1.37/0.60  fof(f14,axiom,(
% 1.37/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.60  fof(f62,plain,(
% 1.37/0.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.37/0.60    inference(cnf_transformation,[],[f40])).
% 1.37/0.60  fof(f40,plain,(
% 1.37/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.37/0.60    inference(flattening,[],[f39])).
% 1.37/0.60  fof(f39,plain,(
% 1.37/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.37/0.60    inference(nnf_transformation,[],[f26])).
% 1.37/0.60  fof(f26,plain,(
% 1.37/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.37/0.60    inference(ennf_transformation,[],[f16])).
% 1.37/0.60  fof(f16,axiom,(
% 1.37/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.37/0.60  fof(f78,plain,(
% 1.37/0.60    r1_tarski(k3_xboole_0(sK1,sK2),k1_enumset1(sK4,sK4,sK4))),
% 1.37/0.60    inference(definition_unfolding,[],[f42,f77])).
% 1.37/0.60  fof(f42,plain,(
% 1.37/0.60    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 1.37/0.60    inference(cnf_transformation,[],[f30])).
% 1.37/0.60  fof(f90,plain,(
% 1.37/0.60    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.37/0.60    inference(equality_resolution,[],[f80])).
% 1.37/0.60  fof(f80,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.37/0.60    inference(definition_unfolding,[],[f55,f76])).
% 1.37/0.60  fof(f55,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.37/0.60    inference(cnf_transformation,[],[f36])).
% 1.37/0.60  fof(f36,plain,(
% 1.37/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.37/0.60    inference(nnf_transformation,[],[f28])).
% 1.37/0.60  fof(f28,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.37/0.60    inference(definition_folding,[],[f12,f27])).
% 1.37/0.60  fof(f12,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.37/0.60  fof(f469,plain,(
% 1.37/0.60    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(sK2,X0) | k1_xboole_0 = k3_xboole_0(sK2,k2_xboole_0(sK3,X0))) )),
% 1.37/0.60    inference(resolution,[],[f129,f73])).
% 1.37/0.60  fof(f129,plain,(
% 1.37/0.60    ( ! [X0] : (r1_xboole_0(sK2,k2_xboole_0(sK3,X0)) | k1_xboole_0 != k3_xboole_0(sK2,X0)) )),
% 1.37/0.60    inference(superposition,[],[f74,f106])).
% 1.37/0.60  fof(f106,plain,(
% 1.37/0.60    ( ! [X0] : (k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,X0)) )),
% 1.37/0.60    inference(resolution,[],[f102,f46])).
% 1.37/0.60  fof(f46,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f22])).
% 1.37/0.60  fof(f22,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.37/0.60    inference(ennf_transformation,[],[f10])).
% 1.37/0.60  fof(f10,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.37/0.60  fof(f102,plain,(
% 1.37/0.60    r1_xboole_0(sK2,sK3)),
% 1.37/0.60    inference(resolution,[],[f44,f48])).
% 1.37/0.60  fof(f74,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f41])).
% 1.37/0.60  % SZS output end Proof for theBenchmark
% 1.37/0.60  % (14849)------------------------------
% 1.37/0.60  % (14849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.60  % (14849)Termination reason: Refutation
% 1.37/0.60  
% 1.37/0.60  % (14849)Memory used [KB]: 2174
% 1.37/0.60  % (14849)Time elapsed: 0.159 s
% 1.37/0.60  % (14849)------------------------------
% 1.37/0.60  % (14849)------------------------------
% 1.37/0.60  % (14847)Success in time 0.239 s
%------------------------------------------------------------------------------
