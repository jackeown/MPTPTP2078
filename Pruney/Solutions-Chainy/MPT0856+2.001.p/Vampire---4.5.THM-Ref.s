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
% DateTime   : Thu Dec  3 12:58:13 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 259 expanded)
%              Number of leaves         :   20 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 539 expanded)
%              Number of equality atoms :   44 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f111,f537])).

fof(f537,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f532,f450])).

fof(f450,plain,(
    ! [X6] : ~ r2_hidden(X6,X6) ),
    inference(subsumption_resolution,[],[f446,f125])).

fof(f125,plain,(
    ! [X2] : ~ r1_tarski(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2)),X2) ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f75,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f40,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f446,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,X6)
      | r1_tarski(k2_xboole_0(X6,k4_enumset1(X6,X6,X6,X6,X6,X6)),X6) ) ),
    inference(superposition,[],[f53,f383])).

fof(f383,plain,(
    ! [X0] : sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0 ),
    inference(subsumption_resolution,[],[f382,f125])).

fof(f382,plain,(
    ! [X0] :
      ( sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0
      | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,(
    ! [X0] :
      ( sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0
      | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0)
      | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) ) ),
    inference(resolution,[],[f158,f53])).

fof(f158,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK4(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11),X10)
      | sK4(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11) = X10
      | r1_tarski(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11) ) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f532,plain,
    ( r2_hidden(sK1,sK1)
    | spl5_1 ),
    inference(resolution,[],[f528,f271])).

fof(f271,plain,(
    ! [X4] :
      ( ~ r2_hidden(k1_mcart_1(sK0),X4)
      | r2_hidden(sK1,X4) ) ),
    inference(resolution,[],[f135,f101])).

fof(f101,plain,(
    r2_hidden(k1_mcart_1(sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f66])).

fof(f37,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f528,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f514,f79])).

fof(f79,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f514,plain,
    ( sK1 = k1_mcart_1(sK0)
    | r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f299,f101])).

fof(f299,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_enumset1(X3,X3,X3,X3,X3,X3))
      | X2 = X3
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f155,f86])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,k2_xboole_0(X4,k4_enumset1(X4,X4,X4,X4,X4,X4)))
      | X3 = X4
      | ~ r2_hidden(X3,X5)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f107,f81])).

fof(f81,plain,
    ( spl5_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f107,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(resolution,[],[f60,f68])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f81,f77])).

fof(f38,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (1931)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (1919)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (1911)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1923)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (1908)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (1909)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1914)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1912)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (1914)Refutation not found, incomplete strategy% (1914)------------------------------
% 0.21/0.54  % (1914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1906)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1905)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (1913)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (1907)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1914)Memory used [KB]: 10618
% 0.21/0.54  % (1914)Time elapsed: 0.127 s
% 0.21/0.54  % (1914)------------------------------
% 0.21/0.54  % (1914)------------------------------
% 0.21/0.54  % (1933)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (1934)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1907)Refutation not found, incomplete strategy% (1907)------------------------------
% 0.21/0.54  % (1907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1907)Memory used [KB]: 10618
% 0.21/0.54  % (1907)Time elapsed: 0.135 s
% 0.21/0.54  % (1907)------------------------------
% 0.21/0.54  % (1907)------------------------------
% 0.21/0.55  % (1927)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (1930)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1905)Refutation not found, incomplete strategy% (1905)------------------------------
% 0.21/0.55  % (1905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1905)Memory used [KB]: 1663
% 0.21/0.55  % (1905)Time elapsed: 0.134 s
% 0.21/0.55  % (1905)------------------------------
% 0.21/0.55  % (1905)------------------------------
% 0.21/0.55  % (1922)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (1926)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (1915)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (1922)Refutation not found, incomplete strategy% (1922)------------------------------
% 1.42/0.55  % (1922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (1922)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (1922)Memory used [KB]: 10618
% 1.42/0.55  % (1922)Time elapsed: 0.140 s
% 1.42/0.55  % (1922)------------------------------
% 1.42/0.55  % (1922)------------------------------
% 1.42/0.55  % (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% 1.42/0.55  % (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (1915)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (1915)Memory used [KB]: 10618
% 1.42/0.55  % (1915)Time elapsed: 0.133 s
% 1.42/0.55  % (1915)------------------------------
% 1.42/0.55  % (1915)------------------------------
% 1.42/0.55  % (1926)Refutation not found, incomplete strategy% (1926)------------------------------
% 1.42/0.55  % (1926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (1926)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (1926)Memory used [KB]: 10746
% 1.42/0.55  % (1926)Time elapsed: 0.139 s
% 1.42/0.55  % (1926)------------------------------
% 1.42/0.55  % (1926)------------------------------
% 1.42/0.55  % (1920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (1929)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (1916)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (1917)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (1935)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (1921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (1932)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.56  % (1916)Refutation not found, incomplete strategy% (1916)------------------------------
% 1.42/0.56  % (1916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (1916)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (1916)Memory used [KB]: 10618
% 1.42/0.56  % (1916)Time elapsed: 0.150 s
% 1.42/0.56  % (1916)------------------------------
% 1.42/0.56  % (1916)------------------------------
% 1.42/0.56  % (1927)Refutation not found, incomplete strategy% (1927)------------------------------
% 1.42/0.56  % (1927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (1924)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.57  % (1927)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (1927)Memory used [KB]: 1663
% 1.61/0.57  % (1927)Time elapsed: 0.161 s
% 1.61/0.57  % (1927)------------------------------
% 1.61/0.57  % (1927)------------------------------
% 1.61/0.57  % (1910)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.59  % (1928)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.61/0.59  % (1918)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.59  % (1933)Refutation found. Thanks to Tanya!
% 1.61/0.59  % SZS status Theorem for theBenchmark
% 1.61/0.59  % SZS output start Proof for theBenchmark
% 1.61/0.59  fof(f538,plain,(
% 1.61/0.59    $false),
% 1.61/0.59    inference(avatar_sat_refutation,[],[f84,f111,f537])).
% 1.61/0.59  fof(f537,plain,(
% 1.61/0.59    spl5_1),
% 1.61/0.59    inference(avatar_contradiction_clause,[],[f536])).
% 1.61/0.59  fof(f536,plain,(
% 1.61/0.59    $false | spl5_1),
% 1.61/0.59    inference(subsumption_resolution,[],[f532,f450])).
% 1.61/0.59  fof(f450,plain,(
% 1.61/0.59    ( ! [X6] : (~r2_hidden(X6,X6)) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f446,f125])).
% 1.61/0.59  fof(f125,plain,(
% 1.61/0.59    ( ! [X2] : (~r1_tarski(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2)),X2)) )),
% 1.61/0.59    inference(resolution,[],[f75,f57])).
% 1.61/0.59  fof(f57,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f23])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f14])).
% 1.61/0.59  fof(f14,axiom,(
% 1.61/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.61/0.59  fof(f75,plain,(
% 1.61/0.59    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))) )),
% 1.61/0.59    inference(equality_resolution,[],[f70])).
% 1.61/0.59  fof(f70,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1))) | X0 != X1) )),
% 1.61/0.59    inference(definition_unfolding,[],[f56,f67])).
% 1.61/0.59  fof(f67,plain,(
% 1.61/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f40,f66])).
% 1.61/0.59  fof(f66,plain,(
% 1.61/0.59    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f39,f65])).
% 1.61/0.59  fof(f65,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f43,f64])).
% 1.61/0.59  fof(f64,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f58,f63])).
% 1.61/0.59  fof(f63,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f61,f62])).
% 1.61/0.59  fof(f62,plain,(
% 1.61/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f10])).
% 1.61/0.59  fof(f10,axiom,(
% 1.61/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.61/0.59  fof(f61,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.61/0.59  fof(f58,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.59  fof(f43,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f7])).
% 1.61/0.59  fof(f7,axiom,(
% 1.61/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.59  fof(f39,plain,(
% 1.61/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f6])).
% 1.61/0.59  fof(f6,axiom,(
% 1.61/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.59  fof(f40,plain,(
% 1.61/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f12])).
% 1.61/0.59  fof(f12,axiom,(
% 1.61/0.59    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.61/0.59  fof(f56,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f36])).
% 1.61/0.59  fof(f36,plain,(
% 1.61/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.61/0.59    inference(flattening,[],[f35])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.61/0.59    inference(nnf_transformation,[],[f13])).
% 1.61/0.59  fof(f13,axiom,(
% 1.61/0.59    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.61/0.59  fof(f446,plain,(
% 1.61/0.59    ( ! [X6] : (~r2_hidden(X6,X6) | r1_tarski(k2_xboole_0(X6,k4_enumset1(X6,X6,X6,X6,X6,X6)),X6)) )),
% 1.61/0.59    inference(superposition,[],[f53,f383])).
% 1.61/0.59  fof(f383,plain,(
% 1.61/0.59    ( ! [X0] : (sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f382,f125])).
% 1.61/0.59  fof(f382,plain,(
% 1.61/0.59    ( ! [X0] : (sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0 | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0)) )),
% 1.61/0.59    inference(duplicate_literal_removal,[],[f370])).
% 1.61/0.59  fof(f370,plain,(
% 1.61/0.59    ( ! [X0] : (sK4(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) = X0 | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0) | r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X0)) )),
% 1.61/0.59    inference(resolution,[],[f158,f53])).
% 1.61/0.59  fof(f158,plain,(
% 1.61/0.59    ( ! [X10,X11] : (r2_hidden(sK4(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11),X10) | sK4(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11) = X10 | r1_tarski(k2_xboole_0(X10,k4_enumset1(X10,X10,X10,X10,X10,X10)),X11)) )),
% 1.61/0.59    inference(resolution,[],[f72,f52])).
% 1.61/0.59  fof(f52,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f34])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.61/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.61/0.59    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.61/0.59    inference(rectify,[],[f31])).
% 1.61/0.59  fof(f31,plain,(
% 1.61/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.61/0.59    inference(nnf_transformation,[],[f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.61/0.59    inference(ennf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.61/0.59  fof(f72,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.61/0.59    inference(definition_unfolding,[],[f54,f67])).
% 1.61/0.59  fof(f54,plain,(
% 1.61/0.59    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f36])).
% 1.61/0.59  fof(f53,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f34])).
% 1.61/0.59  fof(f532,plain,(
% 1.61/0.59    r2_hidden(sK1,sK1) | spl5_1),
% 1.61/0.59    inference(resolution,[],[f528,f271])).
% 1.61/0.59  fof(f271,plain,(
% 1.61/0.59    ( ! [X4] : (~r2_hidden(k1_mcart_1(sK0),X4) | r2_hidden(sK1,X4)) )),
% 1.61/0.59    inference(resolution,[],[f135,f101])).
% 1.61/0.59  fof(f101,plain,(
% 1.61/0.59    r2_hidden(k1_mcart_1(sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.61/0.59    inference(resolution,[],[f59,f68])).
% 1.61/0.59  fof(f68,plain,(
% 1.61/0.59    r2_hidden(sK0,k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.61/0.59    inference(definition_unfolding,[],[f37,f66])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.61/0.60    inference(cnf_transformation,[],[f26])).
% 1.61/0.60  fof(f26,plain,(
% 1.61/0.60    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).
% 1.61/0.60  fof(f25,plain,(
% 1.61/0.60    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f19,plain,(
% 1.61/0.60    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.61/0.60    inference(ennf_transformation,[],[f17])).
% 1.61/0.60  fof(f17,negated_conjecture,(
% 1.61/0.60    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.61/0.60    inference(negated_conjecture,[],[f16])).
% 1.61/0.60  fof(f16,conjecture,(
% 1.61/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.61/0.60  fof(f59,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f24])).
% 1.61/0.60  fof(f24,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.61/0.60    inference(ennf_transformation,[],[f15])).
% 1.61/0.60  fof(f15,axiom,(
% 1.61/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.61/0.60  fof(f135,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.61/0.60    inference(resolution,[],[f69,f46])).
% 1.61/0.60  fof(f46,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f28])).
% 1.61/0.60  fof(f28,plain,(
% 1.61/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).
% 1.61/0.60  fof(f27,plain,(
% 1.61/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f20,plain,(
% 1.61/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.61/0.60    inference(ennf_transformation,[],[f18])).
% 1.61/0.60  fof(f18,plain,(
% 1.61/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.61/0.60    inference(rectify,[],[f3])).
% 1.61/0.60  fof(f3,axiom,(
% 1.61/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.61/0.60  fof(f69,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.61/0.60    inference(definition_unfolding,[],[f47,f66])).
% 1.61/0.60  fof(f47,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f21])).
% 1.61/0.60  fof(f21,plain,(
% 1.61/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.61/0.60    inference(ennf_transformation,[],[f11])).
% 1.61/0.60  fof(f11,axiom,(
% 1.61/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.61/0.60  fof(f528,plain,(
% 1.61/0.60    r2_hidden(k1_mcart_1(sK0),sK1) | spl5_1),
% 1.61/0.60    inference(subsumption_resolution,[],[f514,f79])).
% 1.61/0.60  fof(f79,plain,(
% 1.61/0.60    sK1 != k1_mcart_1(sK0) | spl5_1),
% 1.61/0.60    inference(avatar_component_clause,[],[f77])).
% 1.61/0.60  fof(f77,plain,(
% 1.61/0.60    spl5_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.61/0.60  fof(f514,plain,(
% 1.61/0.60    sK1 = k1_mcart_1(sK0) | r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.61/0.60    inference(resolution,[],[f299,f101])).
% 1.61/0.60  fof(f299,plain,(
% 1.61/0.60    ( ! [X2,X3] : (~r2_hidden(X2,k4_enumset1(X3,X3,X3,X3,X3,X3)) | X2 = X3 | r2_hidden(X2,X3)) )),
% 1.61/0.60    inference(resolution,[],[f155,f86])).
% 1.61/0.60  fof(f86,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.61/0.60    inference(superposition,[],[f41,f42])).
% 1.61/0.60  fof(f42,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f1])).
% 1.61/0.60  fof(f1,axiom,(
% 1.61/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.61/0.60  fof(f41,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f5])).
% 1.61/0.60  fof(f5,axiom,(
% 1.61/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.60  fof(f155,plain,(
% 1.61/0.60    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_xboole_0(X4,k4_enumset1(X4,X4,X4,X4,X4,X4))) | X3 = X4 | ~r2_hidden(X3,X5) | r2_hidden(X3,X4)) )),
% 1.61/0.60    inference(resolution,[],[f72,f51])).
% 1.61/0.60  fof(f51,plain,(
% 1.61/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f34])).
% 1.61/0.60  fof(f111,plain,(
% 1.61/0.60    spl5_2),
% 1.61/0.60    inference(avatar_split_clause,[],[f107,f81])).
% 1.61/0.60  fof(f81,plain,(
% 1.61/0.60    spl5_2 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.61/0.60  fof(f107,plain,(
% 1.61/0.60    r2_hidden(k2_mcart_1(sK0),sK2)),
% 1.61/0.60    inference(resolution,[],[f60,f68])).
% 1.61/0.60  fof(f60,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f24])).
% 1.61/0.60  fof(f84,plain,(
% 1.61/0.60    ~spl5_1 | ~spl5_2),
% 1.61/0.60    inference(avatar_split_clause,[],[f38,f81,f77])).
% 1.61/0.60  fof(f38,plain,(
% 1.61/0.60    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 1.61/0.60    inference(cnf_transformation,[],[f26])).
% 1.61/0.60  % SZS output end Proof for theBenchmark
% 1.61/0.60  % (1933)------------------------------
% 1.61/0.60  % (1933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (1933)Termination reason: Refutation
% 1.61/0.60  
% 1.61/0.60  % (1933)Memory used [KB]: 6524
% 1.61/0.60  % (1933)Time elapsed: 0.183 s
% 1.61/0.60  % (1933)------------------------------
% 1.61/0.60  % (1933)------------------------------
% 1.61/0.60  % (1904)Success in time 0.226 s
%------------------------------------------------------------------------------
