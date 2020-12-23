%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 54.31s
% Output     : Refutation 54.31s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 812 expanded)
%              Number of leaves         :   19 ( 231 expanded)
%              Depth                    :   18
%              Number of atoms          :  421 (3386 expanded)
%              Number of equality atoms :   85 ( 680 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4185,f7173,f62100])).

fof(f62100,plain,
    ( ~ spl5_9
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f62099])).

fof(f62099,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f61956,f61959])).

fof(f61959,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(trivial_inequality_removal,[],[f61958])).

fof(f61958,plain,
    ( sK1 != sK1
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(duplicate_literal_removal,[],[f61622])).

fof(f61622,plain,
    ( sK1 != sK1
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(superposition,[],[f10354,f10693])).

fof(f10693,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f10692,f9714])).

fof(f9714,plain,
    ( sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(backward_demodulation,[],[f108,f9707])).

fof(f9707,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f332,f8061,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f8061,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f7842,f7842,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f7842,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f46,f7030,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f7030,plain,
    ( r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f7029])).

fof(f7029,plain,
    ( spl5_44
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f46,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f332,plain,
    ( r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl5_9
  <=> r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f108,plain,(
    sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) ),
    inference(unit_resulting_resolution,[],[f100,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f100,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f46,f86])).

fof(f10692,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f9928,f74])).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f9928,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(backward_demodulation,[],[f6953,f9707])).

fof(f6953,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_9 ),
    inference(superposition,[],[f565,f4188])).

fof(f4188,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f332,f79])).

fof(f565,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0))) ),
    inference(forward_demodulation,[],[f547,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f547,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0)) ),
    inference(superposition,[],[f73,f108])).

fof(f10354,plain,
    ( ! [X0] :
        ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),X0)
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f10353,f9707])).

fof(f10353,plain,
    ( ! [X0] :
        ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f9718,f9707])).

fof(f9718,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
        | sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(backward_demodulation,[],[f128,f9707])).

fof(f128,plain,(
    ! [X0] :
      ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0))
      | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0) ) ),
    inference(forward_demodulation,[],[f118,f73])).

fof(f118,plain,(
    ! [X0] :
      ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0)
      | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0) ) ),
    inference(superposition,[],[f78,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f78,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))) ),
    inference(definition_unfolding,[],[f47,f76,f56,f77,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f61956,plain,
    ( ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(trivial_inequality_removal,[],[f61955])).

fof(f61955,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(duplicate_literal_removal,[],[f61624])).

fof(f61624,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(superposition,[],[f10358,f10693])).

fof(f10358,plain,
    ( ! [X2] :
        ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X2))
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),X2)
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0)) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f10357,f9707])).

fof(f10357,plain,
    ( ! [X2] :
        ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X2))
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0))
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f9720,f9707])).

fof(f9720,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0))
        | sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2))
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2) )
    | ~ spl5_9
    | ~ spl5_44 ),
    inference(backward_demodulation,[],[f131,f9707])).

fof(f131,plain,(
    ! [X2] :
      ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2))
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0))
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2) ) ),
    inference(forward_demodulation,[],[f130,f73])).

fof(f130,plain,(
    ! [X2] :
      ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2)
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0))
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2) ) ),
    inference(subsumption_resolution,[],[f120,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    ! [X2] :
      ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2)
      | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0))
      | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2) ) ),
    inference(superposition,[],[f78,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7173,plain,(
    spl5_44 ),
    inference(avatar_contradiction_clause,[],[f7150])).

fof(f7150,plain,
    ( $false
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f96,f7031,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7031,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl5_44 ),
    inference(avatar_component_clause,[],[f7029])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4185,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f4184])).

fof(f4184,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f4167,f533])).

fof(f533,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f333,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f333,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f331])).

fof(f4167,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f532,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f532,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f333,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20995)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (20974)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (20973)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (20981)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (20977)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (20994)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (20985)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (20975)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (20987)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (20976)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (21002)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (20979)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (20986)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (20982)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (21000)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (20990)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (20997)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (20992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (20984)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (20996)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (20998)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (20980)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (20978)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (20989)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (20988)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (20983)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (20991)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (20999)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (21001)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (20993)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.75/0.59  % (20993)Refutation not found, incomplete strategy% (20993)------------------------------
% 1.75/0.59  % (20993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (20993)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.59  
% 1.75/0.59  % (20993)Memory used [KB]: 10746
% 1.75/0.59  % (20993)Time elapsed: 0.190 s
% 1.75/0.59  % (20993)------------------------------
% 1.75/0.59  % (20993)------------------------------
% 2.73/0.75  % (21003)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.16/0.83  % (20978)Time limit reached!
% 3.16/0.83  % (20978)------------------------------
% 3.16/0.83  % (20978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.83  % (20978)Termination reason: Time limit
% 3.16/0.83  
% 3.16/0.83  % (20978)Memory used [KB]: 8571
% 3.16/0.83  % (20978)Time elapsed: 0.427 s
% 3.16/0.83  % (20978)------------------------------
% 3.16/0.83  % (20978)------------------------------
% 4.05/0.91  % (20990)Time limit reached!
% 4.05/0.91  % (20990)------------------------------
% 4.05/0.91  % (20990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.91  % (20990)Termination reason: Time limit
% 4.05/0.91  % (20990)Termination phase: Saturation
% 4.05/0.91  
% 4.05/0.91  % (20990)Memory used [KB]: 13688
% 4.05/0.91  % (20990)Time elapsed: 0.500 s
% 4.05/0.91  % (20990)------------------------------
% 4.05/0.91  % (20990)------------------------------
% 4.05/0.91  % (20983)Time limit reached!
% 4.05/0.91  % (20983)------------------------------
% 4.05/0.91  % (20983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.91  % (20983)Termination reason: Time limit
% 4.05/0.91  % (20983)Termination phase: Saturation
% 4.05/0.91  
% 4.05/0.91  % (20983)Memory used [KB]: 13816
% 4.05/0.91  % (20983)Time elapsed: 0.500 s
% 4.05/0.91  % (20983)------------------------------
% 4.05/0.91  % (20983)------------------------------
% 4.05/0.91  % (20974)Time limit reached!
% 4.05/0.91  % (20974)------------------------------
% 4.05/0.91  % (20974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (20973)Time limit reached!
% 4.05/0.92  % (20973)------------------------------
% 4.05/0.92  % (20973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (20973)Termination reason: Time limit
% 4.05/0.92  % (20973)Termination phase: Saturation
% 4.05/0.92  
% 4.05/0.92  % (20973)Memory used [KB]: 3709
% 4.05/0.92  % (20973)Time elapsed: 0.500 s
% 4.05/0.92  % (20973)------------------------------
% 4.05/0.92  % (20973)------------------------------
% 4.05/0.92  % (20974)Termination reason: Time limit
% 4.05/0.92  
% 4.05/0.92  % (20974)Memory used [KB]: 9210
% 4.05/0.92  % (20974)Time elapsed: 0.506 s
% 4.05/0.92  % (20974)------------------------------
% 4.05/0.92  % (20974)------------------------------
% 4.37/0.93  % (20985)Time limit reached!
% 4.37/0.93  % (20985)------------------------------
% 4.37/0.93  % (20985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/0.94  % (20985)Termination reason: Time limit
% 4.49/0.94  
% 4.49/0.94  % (20985)Memory used [KB]: 8955
% 4.49/0.94  % (20985)Time elapsed: 0.520 s
% 4.49/0.94  % (20985)------------------------------
% 4.49/0.94  % (20985)------------------------------
% 4.49/0.96  % (21004)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.49/1.01  % (21001)Time limit reached!
% 4.49/1.01  % (21001)------------------------------
% 4.49/1.01  % (21001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/1.01  % (21001)Termination reason: Time limit
% 4.49/1.01  
% 4.49/1.01  % (21001)Memory used [KB]: 9210
% 4.49/1.01  % (21001)Time elapsed: 0.614 s
% 4.49/1.01  % (21001)------------------------------
% 4.49/1.01  % (21001)------------------------------
% 4.81/1.01  % (20989)Time limit reached!
% 4.81/1.01  % (20989)------------------------------
% 4.81/1.01  % (20989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.01  % (20989)Termination reason: Time limit
% 4.81/1.01  
% 4.81/1.01  % (20989)Memory used [KB]: 17782
% 4.81/1.01  % (20989)Time elapsed: 0.609 s
% 4.81/1.01  % (20989)------------------------------
% 4.81/1.01  % (20989)------------------------------
% 4.81/1.03  % (20980)Time limit reached!
% 4.81/1.03  % (20980)------------------------------
% 4.81/1.03  % (20980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.03  % (20980)Termination reason: Time limit
% 4.81/1.03  
% 4.81/1.03  % (20980)Memory used [KB]: 12025
% 4.81/1.03  % (20980)Time elapsed: 0.613 s
% 4.81/1.03  % (20980)------------------------------
% 4.81/1.03  % (20980)------------------------------
% 4.81/1.04  % (21005)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.81/1.04  % (21006)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.81/1.05  % (21008)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.81/1.06  % (21007)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.68/1.15  % (21010)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.68/1.15  % (21012)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.54/1.19  % (21009)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.80/1.23  % (21011)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.80/1.24  % (20994)Time limit reached!
% 6.80/1.24  % (20994)------------------------------
% 6.80/1.24  % (20994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.80/1.25  % (20994)Termination reason: Time limit
% 6.80/1.25  % (20994)Termination phase: Saturation
% 6.80/1.25  
% 6.80/1.25  % (20994)Memory used [KB]: 6268
% 6.80/1.25  % (20994)Time elapsed: 0.800 s
% 6.80/1.25  % (20994)------------------------------
% 6.80/1.25  % (20994)------------------------------
% 7.42/1.35  % (21013)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.42/1.37  % (21006)Time limit reached!
% 7.42/1.37  % (21006)------------------------------
% 7.42/1.37  % (21006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.42/1.37  % (21006)Termination reason: Time limit
% 7.42/1.37  % (21006)Termination phase: Saturation
% 7.42/1.37  
% 7.42/1.37  % (21006)Memory used [KB]: 7675
% 7.42/1.37  % (21006)Time elapsed: 0.400 s
% 7.42/1.37  % (21006)------------------------------
% 7.42/1.37  % (21006)------------------------------
% 7.42/1.37  % (21007)Time limit reached!
% 7.42/1.37  % (21007)------------------------------
% 7.42/1.37  % (21007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.38  % (21007)Termination reason: Time limit
% 7.95/1.38  % (21007)Termination phase: Saturation
% 7.95/1.38  
% 7.95/1.38  % (21007)Memory used [KB]: 14583
% 7.95/1.38  % (21007)Time elapsed: 0.400 s
% 7.95/1.38  % (21007)------------------------------
% 7.95/1.38  % (21007)------------------------------
% 7.95/1.42  % (20975)Time limit reached!
% 7.95/1.42  % (20975)------------------------------
% 7.95/1.42  % (20975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.42  % (20975)Termination reason: Time limit
% 7.95/1.42  
% 7.95/1.42  % (20975)Memory used [KB]: 18166
% 7.95/1.42  % (20975)Time elapsed: 1.016 s
% 7.95/1.42  % (20975)------------------------------
% 7.95/1.42  % (20975)------------------------------
% 8.61/1.49  % (21014)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.04/1.54  % (21015)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.04/1.57  % (21016)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.04/1.61  % (20995)Time limit reached!
% 9.04/1.61  % (20995)------------------------------
% 9.04/1.61  % (20995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.04/1.61  % (20995)Termination reason: Time limit
% 9.04/1.61  
% 9.04/1.61  % (20995)Memory used [KB]: 13048
% 9.04/1.61  % (20995)Time elapsed: 1.207 s
% 9.04/1.61  % (20995)------------------------------
% 9.04/1.61  % (20995)------------------------------
% 9.85/1.61  % (20999)Time limit reached!
% 9.85/1.61  % (20999)------------------------------
% 9.85/1.61  % (20999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.85/1.61  % (20999)Termination reason: Time limit
% 9.85/1.62  % (20999)Termination phase: Saturation
% 9.85/1.62  
% 9.85/1.62  % (20999)Memory used [KB]: 17782
% 9.85/1.62  % (20999)Time elapsed: 1.200 s
% 9.85/1.62  % (20999)------------------------------
% 9.85/1.62  % (20999)------------------------------
% 10.42/1.72  % (20997)Time limit reached!
% 10.42/1.72  % (20997)------------------------------
% 10.42/1.72  % (20997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.72  % (20997)Termination reason: Time limit
% 10.42/1.72  
% 10.42/1.72  % (20997)Memory used [KB]: 16886
% 10.42/1.72  % (20997)Time elapsed: 1.323 s
% 10.42/1.72  % (20997)------------------------------
% 10.42/1.72  % (20997)------------------------------
% 10.42/1.73  % (20988)Time limit reached!
% 10.42/1.73  % (20988)------------------------------
% 10.42/1.73  % (20988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.73  % (20988)Termination reason: Time limit
% 10.42/1.73  
% 10.42/1.73  % (20988)Memory used [KB]: 13176
% 10.42/1.73  % (20988)Time elapsed: 1.307 s
% 10.42/1.73  % (20988)------------------------------
% 10.42/1.73  % (20988)------------------------------
% 10.42/1.73  % (21017)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.08/1.78  % (21018)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.36/1.83  % (21022)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.36/1.84  % (21021)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.95/1.93  % (21000)Time limit reached!
% 11.95/1.93  % (21000)------------------------------
% 11.95/1.93  % (21000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.95/1.93  % (21000)Termination reason: Time limit
% 11.95/1.93  
% 11.95/1.93  % (21000)Memory used [KB]: 17142
% 11.95/1.93  % (21000)Time elapsed: 1.507 s
% 11.95/1.93  % (21000)------------------------------
% 11.95/1.93  % (21000)------------------------------
% 11.95/1.94  % (20977)Time limit reached!
% 11.95/1.94  % (20977)------------------------------
% 11.95/1.94  % (20977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.95/1.94  % (20977)Termination reason: Time limit
% 11.95/1.94  
% 11.95/1.94  % (20977)Memory used [KB]: 20468
% 11.95/1.94  % (20977)Time elapsed: 1.519 s
% 11.95/1.94  % (20977)------------------------------
% 11.95/1.94  % (20977)------------------------------
% 11.95/1.98  % (21015)Time limit reached!
% 11.95/1.98  % (21015)------------------------------
% 11.95/1.98  % (21015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.95/1.98  % (21015)Termination reason: Time limit
% 11.95/1.98  
% 11.95/1.98  % (21015)Memory used [KB]: 7547
% 11.95/1.98  % (21015)Time elapsed: 0.512 s
% 11.95/1.98  % (21015)------------------------------
% 11.95/1.98  % (21015)------------------------------
% 12.46/2.01  % (20984)Time limit reached!
% 12.46/2.01  % (20984)------------------------------
% 12.46/2.01  % (20984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/2.01  % (20984)Termination reason: Time limit
% 12.46/2.01  
% 12.46/2.01  % (20984)Memory used [KB]: 17526
% 12.46/2.01  % (20984)Time elapsed: 1.613 s
% 12.46/2.01  % (20984)------------------------------
% 12.46/2.01  % (20984)------------------------------
% 12.46/2.06  % (21080)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.46/2.07  % (21085)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.07/2.09  % (21117)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.96/2.15  % (21138)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.96/2.17  % (21021)Time limit reached!
% 13.96/2.17  % (21021)------------------------------
% 13.96/2.17  % (21021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.96/2.17  % (21021)Termination reason: Time limit
% 13.96/2.17  
% 13.96/2.17  % (21021)Memory used [KB]: 4989
% 13.96/2.17  % (21021)Time elapsed: 0.433 s
% 13.96/2.17  % (21021)------------------------------
% 13.96/2.17  % (21021)------------------------------
% 14.58/2.26  % (20987)Time limit reached!
% 14.58/2.26  % (20987)------------------------------
% 14.58/2.26  % (20987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.58/2.26  % (20987)Termination reason: Time limit
% 14.58/2.26  
% 14.58/2.26  % (20987)Memory used [KB]: 21108
% 14.58/2.26  % (20987)Time elapsed: 1.811 s
% 14.58/2.26  % (20987)------------------------------
% 14.58/2.26  % (20987)------------------------------
% 14.58/2.27  % (21190)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.26/2.31  % (21009)Time limit reached!
% 15.26/2.31  % (21009)------------------------------
% 15.26/2.31  % (21009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.26/2.33  % (21009)Termination reason: Time limit
% 15.26/2.33  % (21009)Termination phase: Saturation
% 15.26/2.33  
% 15.26/2.33  % (21009)Memory used [KB]: 20212
% 15.26/2.33  % (21009)Time elapsed: 1.200 s
% 15.26/2.33  % (21009)------------------------------
% 15.26/2.33  % (21009)------------------------------
% 15.26/2.36  % (21085)Time limit reached!
% 15.26/2.36  % (21085)------------------------------
% 15.26/2.36  % (21085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.26/2.37  % (21085)Termination reason: Time limit
% 15.26/2.37  
% 15.26/2.37  % (21085)Memory used [KB]: 3582
% 15.26/2.37  % (21085)Time elapsed: 0.404 s
% 15.26/2.37  % (21085)------------------------------
% 15.26/2.37  % (21085)------------------------------
% 16.14/2.41  % (21238)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.19/2.44  % (20991)Time limit reached!
% 16.19/2.44  % (20991)------------------------------
% 16.19/2.44  % (20991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.19/2.44  % (20991)Termination reason: Time limit
% 16.19/2.44  
% 16.19/2.44  % (20991)Memory used [KB]: 18038
% 16.19/2.44  % (20991)Time elapsed: 2.014 s
% 16.19/2.44  % (20991)------------------------------
% 16.19/2.44  % (20991)------------------------------
% 16.19/2.47  % (21257)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.19/2.48  % (20979)Time limit reached!
% 16.19/2.48  % (20979)------------------------------
% 16.19/2.48  % (20979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.19/2.50  % (20979)Termination reason: Time limit
% 16.19/2.50  
% 16.19/2.50  % (20979)Memory used [KB]: 39402
% 16.19/2.50  % (20979)Time elapsed: 2.041 s
% 16.19/2.50  % (20979)------------------------------
% 16.19/2.50  % (20979)------------------------------
% 16.19/2.50  % (21258)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.86/2.52  % (21258)Refutation not found, incomplete strategy% (21258)------------------------------
% 16.86/2.52  % (21258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.86/2.52  % (21258)Termination reason: Refutation not found, incomplete strategy
% 16.86/2.52  
% 16.86/2.52  % (21258)Memory used [KB]: 6268
% 16.86/2.52  % (21258)Time elapsed: 0.107 s
% 16.86/2.52  % (21258)------------------------------
% 16.86/2.52  % (21258)------------------------------
% 16.86/2.56  % (21259)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.36/2.63  % (21260)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 17.36/2.63  % (21260)Refutation not found, incomplete strategy% (21260)------------------------------
% 17.36/2.63  % (21260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.36/2.65  % (21260)Termination reason: Refutation not found, incomplete strategy
% 17.36/2.65  
% 17.36/2.65  % (21260)Memory used [KB]: 10746
% 17.36/2.65  % (21260)Time elapsed: 0.100 s
% 17.36/2.65  % (21260)------------------------------
% 17.36/2.65  % (21260)------------------------------
% 17.36/2.66  % (21005)Time limit reached!
% 17.36/2.66  % (21005)------------------------------
% 17.36/2.66  % (21005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.36/2.66  % (21005)Termination reason: Time limit
% 17.36/2.66  
% 17.36/2.66  % (21005)Memory used [KB]: 18549
% 17.36/2.66  % (21005)Time elapsed: 1.728 s
% 17.36/2.66  % (21005)------------------------------
% 17.36/2.66  % (21005)------------------------------
% 18.78/2.76  % (21011)Time limit reached!
% 18.78/2.76  % (21011)------------------------------
% 18.78/2.76  % (21011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.78/2.78  % (21257)Time limit reached!
% 18.78/2.78  % (21257)------------------------------
% 18.78/2.78  % (21257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.78/2.78  % (21257)Termination reason: Time limit
% 18.78/2.78  
% 18.78/2.78  % (21257)Memory used [KB]: 9978
% 18.78/2.78  % (21257)Time elapsed: 0.421 s
% 18.78/2.78  % (21257)------------------------------
% 18.78/2.78  % (21257)------------------------------
% 18.78/2.79  % (21011)Termination reason: Time limit
% 18.78/2.79  % (21011)Termination phase: Saturation
% 18.78/2.79  
% 18.78/2.79  % (21011)Memory used [KB]: 7419
% 18.78/2.79  % (21011)Time elapsed: 1.700 s
% 18.78/2.79  % (21011)------------------------------
% 18.78/2.79  % (21011)------------------------------
% 19.56/2.86  % (21018)Time limit reached!
% 19.56/2.86  % (21018)------------------------------
% 19.56/2.86  % (21018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.56/2.86  % (21018)Termination reason: Time limit
% 19.56/2.86  % (21018)Termination phase: Saturation
% 19.56/2.86  
% 19.56/2.86  % (21018)Memory used [KB]: 14711
% 19.56/2.86  % (21018)Time elapsed: 1.213 s
% 19.56/2.86  % (21018)------------------------------
% 19.56/2.86  % (21018)------------------------------
% 19.56/2.89  % (21259)Time limit reached!
% 19.56/2.89  % (21259)------------------------------
% 19.56/2.89  % (21259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.10/2.90  % (20981)Time limit reached!
% 20.10/2.90  % (20981)------------------------------
% 20.10/2.90  % (20981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.10/2.90  % (20981)Termination reason: Time limit
% 20.10/2.90  % (20981)Termination phase: Saturation
% 20.10/2.90  
% 20.10/2.90  % (20981)Memory used [KB]: 21364
% 20.10/2.90  % (20981)Time elapsed: 2.500 s
% 20.10/2.90  % (20981)------------------------------
% 20.10/2.90  % (20981)------------------------------
% 20.10/2.91  % (21259)Termination reason: Time limit
% 20.10/2.91  % (21259)Termination phase: Saturation
% 20.10/2.91  
% 20.10/2.91  % (21259)Memory used [KB]: 11001
% 20.10/2.91  % (21259)Time elapsed: 0.400 s
% 20.10/2.91  % (21259)------------------------------
% 20.10/2.91  % (21259)------------------------------
% 23.28/3.30  % (20992)Time limit reached!
% 23.28/3.30  % (20992)------------------------------
% 23.28/3.30  % (20992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.28/3.30  % (20992)Termination reason: Time limit
% 23.28/3.30  
% 23.28/3.30  % (20992)Memory used [KB]: 18933
% 23.28/3.30  % (20992)Time elapsed: 2.860 s
% 23.28/3.30  % (20992)------------------------------
% 23.28/3.30  % (20992)------------------------------
% 23.54/3.32  % (21080)Time limit reached!
% 23.54/3.32  % (21080)------------------------------
% 23.54/3.32  % (21080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.54/3.32  % (21080)Termination reason: Time limit
% 23.54/3.32  % (21080)Termination phase: Saturation
% 23.54/3.32  
% 23.54/3.32  % (21080)Memory used [KB]: 12920
% 23.54/3.32  % (21080)Time elapsed: 1.300 s
% 23.54/3.32  % (21080)------------------------------
% 23.54/3.32  % (21080)------------------------------
% 23.69/3.40  % (20986)Time limit reached!
% 23.69/3.40  % (20986)------------------------------
% 23.69/3.40  % (20986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.69/3.41  % (20986)Termination reason: Time limit
% 23.69/3.41  % (20986)Termination phase: Saturation
% 23.69/3.41  
% 23.69/3.41  % (20986)Memory used [KB]: 28272
% 23.69/3.41  % (20986)Time elapsed: 3.0000 s
% 23.69/3.41  % (20986)------------------------------
% 23.69/3.41  % (20986)------------------------------
% 26.09/3.67  % (21004)Time limit reached!
% 26.09/3.67  % (21004)------------------------------
% 26.09/3.67  % (21004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.09/3.68  % (21004)Termination reason: Time limit
% 26.09/3.68  
% 26.09/3.68  % (21004)Memory used [KB]: 22259
% 26.09/3.68  % (21004)Time elapsed: 2.812 s
% 26.09/3.68  % (21004)------------------------------
% 26.09/3.68  % (21004)------------------------------
% 31.49/4.34  % (21002)Time limit reached!
% 31.49/4.34  % (21002)------------------------------
% 31.49/4.34  % (21002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.49/4.35  % (21002)Termination reason: Time limit
% 31.49/4.35  % (21002)Termination phase: Saturation
% 31.49/4.35  
% 31.49/4.35  % (21002)Memory used [KB]: 44775
% 31.49/4.35  % (21002)Time elapsed: 3.900 s
% 31.49/4.35  % (21002)------------------------------
% 31.49/4.35  % (21002)------------------------------
% 36.84/5.00  % (20982)Time limit reached!
% 36.84/5.00  % (20982)------------------------------
% 36.84/5.00  % (20982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.84/5.00  % (20982)Termination reason: Time limit
% 36.84/5.00  % (20982)Termination phase: Saturation
% 36.84/5.00  
% 36.84/5.00  % (20982)Memory used [KB]: 41065
% 36.84/5.00  % (20982)Time elapsed: 4.600 s
% 36.84/5.00  % (20982)------------------------------
% 36.84/5.00  % (20982)------------------------------
% 37.92/5.19  % (21017)Time limit reached!
% 37.92/5.19  % (21017)------------------------------
% 37.92/5.19  % (21017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.92/5.19  % (21017)Termination reason: Time limit
% 37.92/5.19  % (21017)Termination phase: Saturation
% 37.92/5.19  
% 37.92/5.19  % (21017)Memory used [KB]: 69082
% 37.92/5.19  % (21017)Time elapsed: 3.500 s
% 37.92/5.19  % (21017)------------------------------
% 37.92/5.19  % (21017)------------------------------
% 41.71/5.61  % (20976)Time limit reached!
% 41.71/5.61  % (20976)------------------------------
% 41.71/5.61  % (20976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.71/5.62  % (20976)Termination reason: Time limit
% 41.71/5.62  % (20976)Termination phase: Saturation
% 41.71/5.62  
% 41.71/5.62  % (20976)Memory used [KB]: 41960
% 41.71/5.62  % (20976)Time elapsed: 5.200 s
% 41.71/5.62  % (20976)------------------------------
% 41.71/5.62  % (20976)------------------------------
% 48.92/6.55  % (21010)Time limit reached!
% 48.92/6.55  % (21010)------------------------------
% 48.92/6.55  % (21010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 48.92/6.55  % (21010)Termination reason: Time limit
% 48.92/6.55  % (21010)Termination phase: Saturation
% 48.92/6.55  
% 48.92/6.55  % (21010)Memory used [KB]: 95307
% 48.92/6.55  % (21010)Time elapsed: 5.500 s
% 48.92/6.55  % (21010)------------------------------
% 48.92/6.55  % (21010)------------------------------
% 54.31/7.17  % (21022)Refutation found. Thanks to Tanya!
% 54.31/7.17  % SZS status Theorem for theBenchmark
% 54.31/7.17  % SZS output start Proof for theBenchmark
% 54.31/7.18  fof(f62233,plain,(
% 54.31/7.18    $false),
% 54.31/7.18    inference(avatar_sat_refutation,[],[f4185,f7173,f62100])).
% 54.31/7.18  fof(f62100,plain,(
% 54.31/7.18    ~spl5_9 | ~spl5_44),
% 54.31/7.18    inference(avatar_contradiction_clause,[],[f62099])).
% 54.31/7.18  fof(f62099,plain,(
% 54.31/7.18    $false | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(subsumption_resolution,[],[f61956,f61959])).
% 54.31/7.18  fof(f61959,plain,(
% 54.31/7.18    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(trivial_inequality_removal,[],[f61958])).
% 54.31/7.18  fof(f61958,plain,(
% 54.31/7.18    sK1 != sK1 | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(duplicate_literal_removal,[],[f61622])).
% 54.31/7.18  fof(f61622,plain,(
% 54.31/7.18    sK1 != sK1 | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(superposition,[],[f10354,f10693])).
% 54.31/7.18  fof(f10693,plain,(
% 54.31/7.18    sK1 = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f10692,f9714])).
% 54.31/7.18  fof(f9714,plain,(
% 54.31/7.18    sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(backward_demodulation,[],[f108,f9707])).
% 54.31/7.18  fof(f9707,plain,(
% 54.31/7.18    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f332,f8061,f72])).
% 54.31/7.18  fof(f72,plain,(
% 54.31/7.18    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f45])).
% 54.31/7.18  fof(f45,plain,(
% 54.31/7.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 54.31/7.18    inference(flattening,[],[f44])).
% 54.31/7.18  fof(f44,plain,(
% 54.31/7.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 54.31/7.18    inference(nnf_transformation,[],[f5])).
% 54.31/7.18  fof(f5,axiom,(
% 54.31/7.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 54.31/7.18  fof(f8061,plain,(
% 54.31/7.18    r1_tarski(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl5_44),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f7842,f7842,f86])).
% 54.31/7.18  fof(f86,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f60,f75])).
% 54.31/7.18  fof(f75,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f12])).
% 54.31/7.18  fof(f12,axiom,(
% 54.31/7.18    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 54.31/7.18  fof(f60,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f34])).
% 54.31/7.18  fof(f34,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 54.31/7.18    inference(flattening,[],[f33])).
% 54.31/7.18  fof(f33,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 54.31/7.18    inference(nnf_transformation,[],[f19])).
% 54.31/7.18  fof(f19,axiom,(
% 54.31/7.18    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 54.31/7.18  fof(f7842,plain,(
% 54.31/7.18    r2_hidden(sK0,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl5_44),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f46,f7030,f92])).
% 54.31/7.18  fof(f92,plain,(
% 54.31/7.18    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 54.31/7.18    inference(equality_resolution,[],[f63])).
% 54.31/7.18  fof(f63,plain,(
% 54.31/7.18    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 54.31/7.18    inference(cnf_transformation,[],[f39])).
% 54.31/7.18  fof(f39,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 54.31/7.18  fof(f38,plain,(
% 54.31/7.18    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 54.31/7.18    introduced(choice_axiom,[])).
% 54.31/7.18  fof(f37,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(rectify,[],[f36])).
% 54.31/7.18  fof(f36,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(flattening,[],[f35])).
% 54.31/7.18  fof(f35,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(nnf_transformation,[],[f2])).
% 54.31/7.18  fof(f2,axiom,(
% 54.31/7.18    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 54.31/7.18  fof(f7030,plain,(
% 54.31/7.18    r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~spl5_44),
% 54.31/7.18    inference(avatar_component_clause,[],[f7029])).
% 54.31/7.18  fof(f7029,plain,(
% 54.31/7.18    spl5_44 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 54.31/7.18    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 54.31/7.18  fof(f46,plain,(
% 54.31/7.18    r2_hidden(sK0,sK1)),
% 54.31/7.18    inference(cnf_transformation,[],[f27])).
% 54.31/7.18  fof(f27,plain,(
% 54.31/7.18    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 54.31/7.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 54.31/7.18  fof(f26,plain,(
% 54.31/7.18    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 54.31/7.18    introduced(choice_axiom,[])).
% 54.31/7.18  fof(f23,plain,(
% 54.31/7.18    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 54.31/7.18    inference(ennf_transformation,[],[f21])).
% 54.31/7.18  fof(f21,negated_conjecture,(
% 54.31/7.18    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 54.31/7.18    inference(negated_conjecture,[],[f20])).
% 54.31/7.18  fof(f20,conjecture,(
% 54.31/7.18    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 54.31/7.18  fof(f332,plain,(
% 54.31/7.18    r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~spl5_9),
% 54.31/7.18    inference(avatar_component_clause,[],[f331])).
% 54.31/7.18  fof(f331,plain,(
% 54.31/7.18    spl5_9 <=> r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 54.31/7.18    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 54.31/7.18  fof(f108,plain,(
% 54.31/7.18    sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f100,f79])).
% 54.31/7.18  fof(f79,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f48,f76])).
% 54.31/7.18  fof(f76,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 54.31/7.18    inference(definition_unfolding,[],[f49,f56])).
% 54.31/7.18  fof(f56,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.31/7.18    inference(cnf_transformation,[],[f6])).
% 54.31/7.18  fof(f6,axiom,(
% 54.31/7.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 54.31/7.18  fof(f49,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 54.31/7.18    inference(cnf_transformation,[],[f10])).
% 54.31/7.18  fof(f10,axiom,(
% 54.31/7.18    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 54.31/7.18  fof(f48,plain,(
% 54.31/7.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f24])).
% 54.31/7.18  fof(f24,plain,(
% 54.31/7.18    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 54.31/7.18    inference(ennf_transformation,[],[f7])).
% 54.31/7.18  fof(f7,axiom,(
% 54.31/7.18    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 54.31/7.18  fof(f100,plain,(
% 54.31/7.18    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f46,f46,f86])).
% 54.31/7.18  fof(f10692,plain,(
% 54.31/7.18    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f9928,f74])).
% 54.31/7.18  fof(f74,plain,(
% 54.31/7.18    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 54.31/7.18    inference(cnf_transformation,[],[f22])).
% 54.31/7.18  fof(f22,plain,(
% 54.31/7.18    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 54.31/7.18    inference(rectify,[],[f4])).
% 54.31/7.18  fof(f4,axiom,(
% 54.31/7.18    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 54.31/7.18  fof(f9928,plain,(
% 54.31/7.18    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)))) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(backward_demodulation,[],[f6953,f9707])).
% 54.31/7.18  fof(f6953,plain,(
% 54.31/7.18    k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl5_9),
% 54.31/7.18    inference(superposition,[],[f565,f4188])).
% 54.31/7.18  fof(f4188,plain,(
% 54.31/7.18    k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))) | ~spl5_9),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f332,f79])).
% 54.31/7.18  fof(f565,plain,(
% 54.31/7.18    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0)))) )),
% 54.31/7.18    inference(forward_demodulation,[],[f547,f73])).
% 54.31/7.18  fof(f73,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 54.31/7.18    inference(cnf_transformation,[],[f9])).
% 54.31/7.18  fof(f9,axiom,(
% 54.31/7.18    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 54.31/7.18  fof(f547,plain,(
% 54.31/7.18    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0))) )),
% 54.31/7.18    inference(superposition,[],[f73,f108])).
% 54.31/7.18  fof(f10354,plain,(
% 54.31/7.18    ( ! [X0] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),X0) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f10353,f9707])).
% 54.31/7.18  fof(f10353,plain,(
% 54.31/7.18    ( ! [X0] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0)) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f9718,f9707])).
% 54.31/7.18  fof(f9718,plain,(
% 54.31/7.18    ( ! [X0] : (r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0)) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(backward_demodulation,[],[f128,f9707])).
% 54.31/7.18  fof(f128,plain,(
% 54.31/7.18    ( ! [X0] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0)) )),
% 54.31/7.18    inference(forward_demodulation,[],[f118,f73])).
% 54.31/7.18  fof(f118,plain,(
% 54.31/7.18    ( ! [X0] : (sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X0),X0)) )),
% 54.31/7.18    inference(superposition,[],[f78,f82])).
% 54.31/7.18  fof(f82,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f53,f56])).
% 54.31/7.18  fof(f53,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f32])).
% 54.31/7.18  fof(f32,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 54.31/7.18  fof(f31,plain,(
% 54.31/7.18    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 54.31/7.18    introduced(choice_axiom,[])).
% 54.31/7.18  fof(f30,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(rectify,[],[f29])).
% 54.31/7.18  fof(f29,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(flattening,[],[f28])).
% 54.31/7.18  fof(f28,plain,(
% 54.31/7.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.31/7.18    inference(nnf_transformation,[],[f3])).
% 54.31/7.18  fof(f3,axiom,(
% 54.31/7.18    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 54.31/7.18  fof(f78,plain,(
% 54.31/7.18    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))))),
% 54.31/7.18    inference(definition_unfolding,[],[f47,f76,f56,f77,f77])).
% 54.31/7.18  fof(f77,plain,(
% 54.31/7.18    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f57,f75])).
% 54.31/7.18  fof(f57,plain,(
% 54.31/7.18    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f11])).
% 54.31/7.18  fof(f11,axiom,(
% 54.31/7.18    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 54.31/7.18  fof(f47,plain,(
% 54.31/7.18    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 54.31/7.18    inference(cnf_transformation,[],[f27])).
% 54.31/7.18  fof(f61956,plain,(
% 54.31/7.18    ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(trivial_inequality_removal,[],[f61955])).
% 54.31/7.18  fof(f61955,plain,(
% 54.31/7.18    sK1 != sK1 | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(duplicate_literal_removal,[],[f61624])).
% 54.31/7.18  fof(f61624,plain,(
% 54.31/7.18    sK1 != sK1 | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(superposition,[],[f10358,f10693])).
% 54.31/7.18  fof(f10358,plain,(
% 54.31/7.18    ( ! [X2] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X2)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),X2) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0))) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f10357,f9707])).
% 54.31/7.18  fof(f10357,plain,(
% 54.31/7.18    ( ! [X2] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),X2)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2)) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(forward_demodulation,[],[f9720,f9707])).
% 54.31/7.18  fof(f9720,plain,(
% 54.31/7.18    ( ! [X2] : (~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2),k1_enumset1(sK0,sK0,sK0)) | sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2)) ) | (~spl5_9 | ~spl5_44)),
% 54.31/7.18    inference(backward_demodulation,[],[f131,f9707])).
% 54.31/7.18  fof(f131,plain,(
% 54.31/7.18    ( ! [X2] : (sK1 != k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),X2)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2)) )),
% 54.31/7.18    inference(forward_demodulation,[],[f130,f73])).
% 54.31/7.18  fof(f130,plain,(
% 54.31/7.18    ( ! [X2] : (sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2)) )),
% 54.31/7.18    inference(subsumption_resolution,[],[f120,f90])).
% 54.31/7.18  fof(f90,plain,(
% 54.31/7.18    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 54.31/7.18    inference(equality_resolution,[],[f84])).
% 54.31/7.18  fof(f84,plain,(
% 54.31/7.18    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 54.31/7.18    inference(definition_unfolding,[],[f51,f56])).
% 54.31/7.18  fof(f51,plain,(
% 54.31/7.18    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 54.31/7.18    inference(cnf_transformation,[],[f32])).
% 54.31/7.18  fof(f120,plain,(
% 54.31/7.18    ( ! [X2] : (sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),X2),X2)) )),
% 54.31/7.18    inference(superposition,[],[f78,f80])).
% 54.31/7.18  fof(f80,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f55,f56])).
% 54.31/7.18  fof(f55,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f32])).
% 54.31/7.18  fof(f7173,plain,(
% 54.31/7.18    spl5_44),
% 54.31/7.18    inference(avatar_contradiction_clause,[],[f7150])).
% 54.31/7.18  fof(f7150,plain,(
% 54.31/7.18    $false | spl5_44),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f96,f7031,f88])).
% 54.31/7.18  fof(f88,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2)) )),
% 54.31/7.18    inference(definition_unfolding,[],[f58,f75])).
% 54.31/7.18  fof(f58,plain,(
% 54.31/7.18    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f34])).
% 54.31/7.18  fof(f7031,plain,(
% 54.31/7.18    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl5_44),
% 54.31/7.18    inference(avatar_component_clause,[],[f7029])).
% 54.31/7.18  fof(f96,plain,(
% 54.31/7.18    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 54.31/7.18    inference(equality_resolution,[],[f70])).
% 54.31/7.18  fof(f70,plain,(
% 54.31/7.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 54.31/7.18    inference(cnf_transformation,[],[f45])).
% 54.31/7.18  fof(f4185,plain,(
% 54.31/7.18    spl5_9),
% 54.31/7.18    inference(avatar_contradiction_clause,[],[f4184])).
% 54.31/7.18  fof(f4184,plain,(
% 54.31/7.18    $false | spl5_9),
% 54.31/7.18    inference(subsumption_resolution,[],[f4167,f533])).
% 54.31/7.18  fof(f533,plain,(
% 54.31/7.18    ~r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_9),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f333,f69])).
% 54.31/7.18  fof(f69,plain,(
% 54.31/7.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f43])).
% 54.31/7.18  fof(f43,plain,(
% 54.31/7.18    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.31/7.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 54.31/7.18  fof(f42,plain,(
% 54.31/7.18    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 54.31/7.18    introduced(choice_axiom,[])).
% 54.31/7.18  fof(f41,plain,(
% 54.31/7.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.31/7.18    inference(rectify,[],[f40])).
% 54.31/7.18  fof(f40,plain,(
% 54.31/7.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 54.31/7.18    inference(nnf_transformation,[],[f25])).
% 54.31/7.18  fof(f25,plain,(
% 54.31/7.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 54.31/7.18    inference(ennf_transformation,[],[f1])).
% 54.31/7.18  fof(f1,axiom,(
% 54.31/7.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 54.31/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 54.31/7.18  fof(f333,plain,(
% 54.31/7.18    ~r1_tarski(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_9),
% 54.31/7.18    inference(avatar_component_clause,[],[f331])).
% 54.31/7.18  fof(f4167,plain,(
% 54.31/7.18    r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_9),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f532,f93])).
% 54.31/7.18  fof(f93,plain,(
% 54.31/7.18    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 54.31/7.18    inference(equality_resolution,[],[f62])).
% 54.31/7.18  fof(f62,plain,(
% 54.31/7.18    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 54.31/7.18    inference(cnf_transformation,[],[f39])).
% 54.31/7.18  fof(f532,plain,(
% 54.31/7.18    r2_hidden(sK4(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl5_9),
% 54.31/7.18    inference(unit_resulting_resolution,[],[f333,f68])).
% 54.31/7.18  fof(f68,plain,(
% 54.31/7.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 54.31/7.18    inference(cnf_transformation,[],[f43])).
% 54.31/7.18  % SZS output end Proof for theBenchmark
% 54.31/7.18  % (21022)------------------------------
% 54.31/7.18  % (21022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 54.31/7.18  % (21022)Termination reason: Refutation
% 54.31/7.18  
% 54.31/7.18  % (21022)Memory used [KB]: 40425
% 54.31/7.18  % (21022)Time elapsed: 5.431 s
% 54.31/7.18  % (21022)------------------------------
% 54.31/7.18  % (21022)------------------------------
% 54.44/7.19  % (20972)Success in time 6.832 s
%------------------------------------------------------------------------------
