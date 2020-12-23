%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:33 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 253 expanded)
%              Number of leaves         :   20 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 ( 600 expanded)
%              Number of equality atoms :   13 (  80 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f279,f2186])).

fof(f2186,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f2182])).

fof(f2182,plain,
    ( $false
    | ~ spl6_1 ),
    inference(resolution,[],[f2181,f39])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f31])).

fof(f31,plain,
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f2181,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f2178,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2178,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f2150,f70])).

fof(f70,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f2150,plain,
    ( ! [X8] :
        ( r1_xboole_0(sK1,k2_xboole_0(sK0,X8))
        | ~ r1_xboole_0(sK1,X8) )
    | ~ spl6_1 ),
    inference(resolution,[],[f1197,f381])).

fof(f381,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f317,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f317,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_xboole_0(X3,X5)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f137,f76])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | ~ r1_tarski(X2,X1)
      | r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f68,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f46,f46])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1197,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,X0))),X0)
        | r1_xboole_0(sK1,k2_xboole_0(sK0,X0)) )
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1189,f63])).

fof(f1189,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK0,X0),sK1)),X0)
        | r1_xboole_0(sK1,k2_xboole_0(sK0,X0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f353,f593])).

fof(f593,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f395,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f395,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK4(X6,X7),X8)
      | r1_xboole_0(X6,X7)
      | ~ r1_xboole_0(X8,X6) ) ),
    inference(resolution,[],[f120,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f120,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
      | r1_xboole_0(X2,X3)
      | ~ r2_hidden(sK4(X2,X3),X4) ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f353,plain,
    ( ! [X12,X13] :
        ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X12),X13),sK1)
        | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X12),X13),X12) )
    | ~ spl6_1 ),
    inference(resolution,[],[f81,f320])).

fof(f320,plain,
    ( ! [X11] :
        ( ~ r1_tarski(X11,sK0)
        | r1_xboole_0(X11,sK1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f137,f289])).

fof(f289,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_1 ),
    inference(resolution,[],[f187,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f67,f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f187,plain,
    ( ! [X3] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_1
  <=> ! [X3] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0)
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1) ) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f279,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f274,f39])).

fof(f274,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_2 ),
    inference(resolution,[],[f270,f53])).

fof(f270,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_2 ),
    inference(resolution,[],[f265,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f265,plain,
    ( r2_hidden(sK3,sK1)
    | spl6_2 ),
    inference(resolution,[],[f246,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f246,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl6_2 ),
    inference(resolution,[],[f196,f92])).

fof(f92,plain,(
    ! [X8,X7,X9] :
      ( r1_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,X7)))
      | ~ r1_xboole_0(X9,X7) ) ),
    inference(superposition,[],[f69,f63])).

fof(f196,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl6_2 ),
    inference(resolution,[],[f191,f53])).

fof(f191,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_2
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f192,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f183,f189,f186])).

fof(f183,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
      | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3) ) ),
    inference(resolution,[],[f171,f62])).

fof(f62,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f37,f46,f60])).

fof(f37,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f171,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X2,X4) ) ),
    inference(resolution,[],[f92,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:57:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (10637)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10638)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (10639)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (10649)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10640)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10643)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (10650)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (10647)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (10645)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (10641)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (10644)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (10644)Refutation not found, incomplete strategy% (10644)------------------------------
% 0.21/0.49  % (10644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10644)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10644)Memory used [KB]: 10618
% 0.21/0.49  % (10644)Time elapsed: 0.071 s
% 0.21/0.49  % (10644)------------------------------
% 0.21/0.49  % (10644)------------------------------
% 0.21/0.49  % (10635)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (10636)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10634)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10642)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10651)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (10646)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (10633)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.64/0.57  % (10637)Refutation found. Thanks to Tanya!
% 1.64/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f2187,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(avatar_sat_refutation,[],[f192,f279,f2186])).
% 1.64/0.57  fof(f2186,plain,(
% 1.64/0.57    ~spl6_1),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f2182])).
% 1.64/0.57  fof(f2182,plain,(
% 1.64/0.57    $false | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f2181,f39])).
% 1.64/0.57  fof(f39,plain,(
% 1.64/0.57    r1_xboole_0(sK2,sK1)),
% 1.64/0.57    inference(cnf_transformation,[],[f32])).
% 1.64/0.57  fof(f32,plain,(
% 1.64/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f31])).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f21,plain,(
% 1.64/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.64/0.57    inference(flattening,[],[f20])).
% 1.64/0.57  fof(f20,plain,(
% 1.64/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.64/0.57    inference(ennf_transformation,[],[f17])).
% 1.64/0.57  fof(f17,negated_conjecture,(
% 1.64/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.64/0.57    inference(negated_conjecture,[],[f16])).
% 1.64/0.57  fof(f16,conjecture,(
% 1.64/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.64/0.57  fof(f2181,plain,(
% 1.64/0.57    ~r1_xboole_0(sK2,sK1) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f2178,f53])).
% 1.64/0.57  fof(f53,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f25])).
% 1.64/0.57  fof(f25,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.64/0.57  fof(f2178,plain,(
% 1.64/0.57    ~r1_xboole_0(sK1,sK2) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f2150,f70])).
% 1.64/0.57  fof(f70,plain,(
% 1.64/0.57    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.64/0.57    inference(resolution,[],[f53,f40])).
% 1.64/0.57  fof(f40,plain,(
% 1.64/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.64/0.57    inference(cnf_transformation,[],[f32])).
% 1.64/0.57  fof(f2150,plain,(
% 1.64/0.57    ( ! [X8] : (r1_xboole_0(sK1,k2_xboole_0(sK0,X8)) | ~r1_xboole_0(sK1,X8)) ) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f1197,f381])).
% 1.64/0.57  fof(f381,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X2) | ~r1_xboole_0(X0,X2)) )),
% 1.64/0.57    inference(resolution,[],[f317,f42])).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.64/0.57  fof(f317,plain,(
% 1.64/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r1_xboole_0(X3,X5) | ~r1_xboole_0(X4,X5)) )),
% 1.64/0.57    inference(resolution,[],[f137,f76])).
% 1.64/0.57  fof(f76,plain,(
% 1.64/0.57    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))) | ~r1_xboole_0(X3,X4)) )),
% 1.64/0.57    inference(resolution,[],[f64,f50])).
% 1.64/0.57  fof(f50,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f35])).
% 1.64/0.57  fof(f35,plain,(
% 1.64/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f23,plain,(
% 1.64/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(ennf_transformation,[],[f19])).
% 1.64/0.57  fof(f19,plain,(
% 1.64/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(rectify,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.64/0.57  fof(f64,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f48,f46])).
% 1.64/0.57  fof(f46,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f7])).
% 1.64/0.57  fof(f7,axiom,(
% 1.64/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.64/0.57  fof(f48,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f34])).
% 1.64/0.57  fof(f34,plain,(
% 1.64/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f33])).
% 1.64/0.57  fof(f33,plain,(
% 1.64/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f22,plain,(
% 1.64/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(ennf_transformation,[],[f18])).
% 1.64/0.57  fof(f18,plain,(
% 1.64/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.57    inference(rectify,[],[f4])).
% 1.64/0.57  fof(f4,axiom,(
% 1.64/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.64/0.57  fof(f137,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | ~r1_tarski(X2,X1) | r1_xboole_0(X2,X0)) )),
% 1.64/0.57    inference(superposition,[],[f68,f63])).
% 1.64/0.57  fof(f63,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f43,f46,f46])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f1])).
% 1.64/0.57  fof(f1,axiom,(
% 1.64/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.64/0.57  fof(f68,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f57,f46])).
% 1.64/0.57  fof(f57,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f29])).
% 1.64/0.57  fof(f29,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.64/0.57  fof(f1197,plain,(
% 1.64/0.57    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,X0))),X0) | r1_xboole_0(sK1,k2_xboole_0(sK0,X0))) ) | ~spl6_1),
% 1.64/0.57    inference(forward_demodulation,[],[f1189,f63])).
% 1.64/0.57  fof(f1189,plain,(
% 1.64/0.57    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK0,X0),sK1)),X0) | r1_xboole_0(sK1,k2_xboole_0(sK0,X0))) ) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f353,f593])).
% 1.64/0.57  fof(f593,plain,(
% 1.64/0.57    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) | r1_xboole_0(X2,X3)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f590])).
% 1.64/0.57  fof(f590,plain,(
% 1.64/0.57    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | ~r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) | r1_xboole_0(X2,X3)) )),
% 1.64/0.57    inference(resolution,[],[f395,f123])).
% 1.64/0.57  fof(f123,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(superposition,[],[f65,f63])).
% 1.64/0.57  fof(f65,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f47,f46])).
% 1.64/0.57  fof(f47,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f34])).
% 1.64/0.57  fof(f395,plain,(
% 1.64/0.57    ( ! [X6,X8,X7] : (~r2_hidden(sK4(X6,X7),X8) | r1_xboole_0(X6,X7) | ~r1_xboole_0(X8,X6)) )),
% 1.64/0.57    inference(resolution,[],[f120,f69])).
% 1.64/0.57  fof(f69,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f58,f46])).
% 1.64/0.57  fof(f58,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f30])).
% 1.64/0.57  fof(f30,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.64/0.57    inference(ennf_transformation,[],[f9])).
% 1.64/0.57  fof(f9,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.64/0.57  fof(f120,plain,(
% 1.64/0.57    ( ! [X4,X2,X3] : (~r1_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(X2,X3))) | r1_xboole_0(X2,X3) | ~r2_hidden(sK4(X2,X3),X4)) )),
% 1.64/0.57    inference(resolution,[],[f65,f51])).
% 1.64/0.57  fof(f51,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f353,plain,(
% 1.64/0.57    ( ! [X12,X13] : (r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X12),X13),sK1) | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X12),X13),X12)) ) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f81,f320])).
% 1.64/0.57  fof(f320,plain,(
% 1.64/0.57    ( ! [X11] : (~r1_tarski(X11,sK0) | r1_xboole_0(X11,sK1)) ) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f137,f289])).
% 1.64/0.57  fof(f289,plain,(
% 1.64/0.57    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_1),
% 1.64/0.57    inference(resolution,[],[f187,f79])).
% 1.64/0.57  fof(f79,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(resolution,[],[f67,f53])).
% 1.64/0.57  fof(f67,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f54,f46])).
% 1.64/0.57  fof(f54,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f26,plain,(
% 1.64/0.57    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f10])).
% 1.64/0.57  fof(f10,axiom,(
% 1.64/0.57    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 1.64/0.57  fof(f187,plain,(
% 1.64/0.57    ( ! [X3] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3)) ) | ~spl6_1),
% 1.64/0.57    inference(avatar_component_clause,[],[f186])).
% 1.64/0.57  fof(f186,plain,(
% 1.64/0.57    spl6_1 <=> ! [X3] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.64/0.57  fof(f81,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0) | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1)) )),
% 1.64/0.57    inference(resolution,[],[f56,f42])).
% 1.64/0.57  fof(f56,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f28])).
% 1.64/0.57  fof(f28,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.64/0.57    inference(flattening,[],[f27])).
% 1.64/0.57  fof(f27,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.64/0.57    inference(ennf_transformation,[],[f8])).
% 1.64/0.57  fof(f8,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.64/0.57  fof(f279,plain,(
% 1.64/0.57    spl6_2),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f275])).
% 1.64/0.57  fof(f275,plain,(
% 1.64/0.57    $false | spl6_2),
% 1.64/0.57    inference(resolution,[],[f274,f39])).
% 1.64/0.57  fof(f274,plain,(
% 1.64/0.57    ~r1_xboole_0(sK2,sK1) | spl6_2),
% 1.64/0.57    inference(resolution,[],[f270,f53])).
% 1.64/0.57  fof(f270,plain,(
% 1.64/0.57    ~r1_xboole_0(sK1,sK2) | spl6_2),
% 1.64/0.57    inference(resolution,[],[f265,f72])).
% 1.64/0.57  fof(f72,plain,(
% 1.64/0.57    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.64/0.57    inference(resolution,[],[f51,f38])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    r2_hidden(sK3,sK2)),
% 1.64/0.57    inference(cnf_transformation,[],[f32])).
% 1.64/0.57  fof(f265,plain,(
% 1.64/0.57    r2_hidden(sK3,sK1) | spl6_2),
% 1.64/0.57    inference(resolution,[],[f246,f66])).
% 1.64/0.57  fof(f66,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f52,f60])).
% 1.64/0.57  fof(f60,plain,(
% 1.64/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f41,f59])).
% 1.64/0.57  fof(f59,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f44,f55])).
% 1.64/0.57  fof(f55,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f14])).
% 1.64/0.57  fof(f14,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,axiom,(
% 1.64/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.57  fof(f41,plain,(
% 1.64/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,axiom,(
% 1.64/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.57  fof(f52,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f24])).
% 1.64/0.57  fof(f24,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f15])).
% 1.64/0.57  fof(f15,axiom,(
% 1.64/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.64/0.57  fof(f246,plain,(
% 1.64/0.57    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl6_2),
% 1.64/0.57    inference(resolution,[],[f196,f92])).
% 1.64/0.57  fof(f92,plain,(
% 1.64/0.57    ( ! [X8,X7,X9] : (r1_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,X7))) | ~r1_xboole_0(X9,X7)) )),
% 1.64/0.57    inference(superposition,[],[f69,f63])).
% 1.64/0.57  fof(f196,plain,(
% 1.64/0.57    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl6_2),
% 1.64/0.57    inference(resolution,[],[f191,f53])).
% 1.64/0.57  fof(f191,plain,(
% 1.64/0.57    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_2),
% 1.64/0.57    inference(avatar_component_clause,[],[f189])).
% 1.64/0.57  fof(f189,plain,(
% 1.64/0.57    spl6_2 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.64/0.57  fof(f192,plain,(
% 1.64/0.57    spl6_1 | ~spl6_2),
% 1.64/0.57    inference(avatar_split_clause,[],[f183,f189,f186])).
% 1.64/0.57  fof(f183,plain,(
% 1.64/0.57    ( ! [X3] : (~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3)) )),
% 1.64/0.57    inference(resolution,[],[f171,f62])).
% 1.64/0.57  fof(f62,plain,(
% 1.64/0.57    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.64/0.57    inference(definition_unfolding,[],[f37,f46,f60])).
% 1.64/0.57  fof(f37,plain,(
% 1.64/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.64/0.57    inference(cnf_transformation,[],[f32])).
% 1.64/0.57  fof(f171,plain,(
% 1.64/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | r1_xboole_0(X2,X4)) )),
% 1.64/0.57    inference(resolution,[],[f92,f68])).
% 1.64/0.57  % SZS output end Proof for theBenchmark
% 1.64/0.57  % (10637)------------------------------
% 1.64/0.57  % (10637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (10637)Termination reason: Refutation
% 1.64/0.57  
% 1.64/0.57  % (10637)Memory used [KB]: 7036
% 1.64/0.57  % (10637)Time elapsed: 0.138 s
% 1.64/0.57  % (10637)------------------------------
% 1.64/0.57  % (10637)------------------------------
% 1.64/0.57  % (10632)Success in time 0.209 s
%------------------------------------------------------------------------------
