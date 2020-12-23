%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  71 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 316 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f19,f100,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK1(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK1(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f100,plain,(
    ~ r2_hidden(sK1(k3_setfam_1(sK0,sK0),sK0),k3_setfam_1(sK0,sK0)) ),
    inference(resolution,[],[f97,f35])).

fof(f35,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k3_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k3_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f14,f17,f16,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k3_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k3_xboole_0(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k3_xboole_0(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (27827)Termination reason: Refutation not found, incomplete strategy
fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k3_xboole_0(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

% (27827)Memory used [KB]: 1535
% (27827)Time elapsed: 0.054 s
% (27827)------------------------------
% (27827)------------------------------
fof(f17,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k3_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k3_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k3_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k3_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

fof(f97,plain,(
    ~ r2_hidden(sK5(sK0,sK0,sK1(k3_setfam_1(sK0,sK0),sK0)),sK0) ),
    inference(resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sQ7_eqProxy(sK5(sK0,sK0,sK1(k3_setfam_1(sK0,sK0),sK0)),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ sQ7_eqProxy(sK5(sK0,sK0,sK1(k3_setfam_1(sK0,sK0),sK0)),X0)
      | r1_setfam_1(k3_setfam_1(sK0,sK0),sK0) ) ),
    inference(resolution,[],[f61,f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(k3_setfam_1(sK0,sK0),sK0),k3_setfam_1(X0,X1))
      | ~ r2_hidden(X2,sK0)
      | ~ sQ7_eqProxy(sK5(X0,X1,sK1(k3_setfam_1(sK0,sK0),sK0)),X2) ) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X0,X8,X1] :
      ( sQ7_eqProxy(k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)),X8)
      | ~ r2_hidden(X8,k3_setfam_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f33,f36])).

fof(f33,plain,(
    ! [X0,X8,X1] :
      ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k3_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X8,X1] :
      ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k3_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ7_eqProxy(k3_xboole_0(X0,X1),sK1(k3_setfam_1(sK0,sK0),sK0))
      | ~ sQ7_eqProxy(X0,X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f57,f19])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_setfam_1(X3,X4)
      | ~ sQ7_eqProxy(k3_xboole_0(X0,X2),sK1(X3,X4))
      | ~ sQ7_eqProxy(X0,X1)
      | ~ r2_hidden(X1,X4) ) ),
    inference(resolution,[],[f56,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ sQ7_eqProxy(X0,X1)
      | ~ sQ7_eqProxy(X2,sK1(X3,X4))
      | r1_setfam_1(X3,X4)
      | ~ r2_hidden(X1,X4) ) ),
    inference(resolution,[],[f52,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK1(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f36])).

fof(f19,plain,(
    ~ r1_setfam_1(k3_setfam_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ r1_setfam_1(k3_setfam_1(sK0,sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] : ~ r1_setfam_1(k3_setfam_1(X0,X0),X0)
   => ~ r1_setfam_1(k3_setfam_1(sK0,sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_setfam_1)).

%------------------------------------------------------------------------------
