%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t20_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:23 EDT 2019

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 215 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(global_subsumption,[],[f44,f50])).

fof(f50,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f18,f19,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t20_xboole_1.p',t19_xboole_1)).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k3_xboole_0(sK1,sK2) != sK0
    & ! [X3] :
        ( r1_tarski(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X3,sK1) )
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK2) != sK0
      & ! [X3] :
          ( r1_tarski(X3,sK0)
          | ~ r1_tarski(X3,sK2)
          | ~ r1_tarski(X3,sK1) )
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t20_xboole_1.p',t20_xboole_1)).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f21,f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/xboole_1__t20_xboole_1.p',d10_xboole_0)).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f28,f33,f20])).

fof(f20,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | r1_tarski(X3,sK0)
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t20_xboole_1.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t20_xboole_1.p',t17_xboole_1)).

fof(f21,plain,(
    k3_xboole_0(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
