%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:45 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 179 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 ( 581 expanded)
%              Number of equality atoms :   17 (  59 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f184,f428])).

fof(f428,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f424,f134])).

fof(f134,plain,
    ( spl6_4
  <=> r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f424,plain,(
    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1)) ),
    inference(resolution,[],[f145,f94])).

fof(f94,plain,(
    r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1)) ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f63,plain,(
    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK1) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f58,plain,(
    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f41,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f26,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(f145,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),X2)
      | r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),X2) ) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))) ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ~ r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f184,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f178,f130])).

fof(f130,plain,
    ( spl6_3
  <=> r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f178,plain,(
    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0)) ),
    inference(resolution,[],[f101,f72])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))))
      | r2_hidden(X0,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f90,f32])).

fof(f90,plain,(
    r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0)) ),
    inference(resolution,[],[f62,f29])).

fof(f62,plain,(
    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0) ),
    inference(resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f28])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f125,f134,f130])).

fof(f125,plain,
    ( ~ r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1))
    | ~ r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0)) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f28])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ~ r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23160)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (23189)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (23181)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (23167)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (23177)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (23164)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (23162)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (23169)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (23172)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (23179)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (23161)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (23161)Refutation not found, incomplete strategy% (23161)------------------------------
% 0.22/0.54  % (23161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23161)Memory used [KB]: 10618
% 0.22/0.54  % (23161)Time elapsed: 0.124 s
% 0.22/0.54  % (23161)------------------------------
% 0.22/0.54  % (23161)------------------------------
% 0.22/0.54  % (23165)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (23184)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (23180)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (23185)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (23171)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (23170)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (23182)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (23168)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (23188)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (23159)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (23175)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (23176)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (23183)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (23180)Refutation not found, incomplete strategy% (23180)------------------------------
% 0.22/0.56  % (23180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23180)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23180)Memory used [KB]: 10746
% 0.22/0.56  % (23180)Time elapsed: 0.148 s
% 0.22/0.56  % (23180)------------------------------
% 0.22/0.56  % (23180)------------------------------
% 0.22/0.56  % (23168)Refutation not found, incomplete strategy% (23168)------------------------------
% 0.22/0.56  % (23168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23168)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23168)Memory used [KB]: 10618
% 0.22/0.56  % (23168)Time elapsed: 0.148 s
% 0.22/0.56  % (23168)------------------------------
% 0.22/0.56  % (23168)------------------------------
% 0.22/0.56  % (23178)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (23187)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (23174)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (23166)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.57  % (23186)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.58  % (23173)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.59  % (23175)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f429,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f137,f184,f428])).
% 1.57/0.59  fof(f428,plain,(
% 1.57/0.59    spl6_4),
% 1.57/0.59    inference(avatar_split_clause,[],[f424,f134])).
% 1.57/0.59  fof(f134,plain,(
% 1.57/0.59    spl6_4 <=> r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.57/0.59  fof(f424,plain,(
% 1.57/0.59    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1))),
% 1.57/0.59    inference(resolution,[],[f145,f94])).
% 1.57/0.59  fof(f94,plain,(
% 1.57/0.59    r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1))),
% 1.57/0.59    inference(resolution,[],[f63,f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,plain,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.57/0.59    inference(ennf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.57/0.59  fof(f63,plain,(
% 1.57/0.59    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK1)),
% 1.57/0.59    inference(resolution,[],[f58,f50])).
% 1.57/0.59  fof(f50,plain,(
% 1.57/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.59    inference(equality_resolution,[],[f47])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.57/0.59    inference(definition_unfolding,[],[f36,f28])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f4])).
% 1.57/0.59  fof(f4,axiom,(
% 1.57/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.59  fof(f36,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.59    inference(cnf_transformation,[],[f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.57/0.59  fof(f24,plain,(
% 1.57/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f23,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.59    inference(rectify,[],[f22])).
% 1.57/0.59  fof(f22,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.59    inference(flattening,[],[f21])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.59    inference(nnf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.57/0.59  fof(f58,plain,(
% 1.57/0.59    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.57/0.59    inference(resolution,[],[f41,f30])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f16])).
% 1.57/0.59  fof(f16,plain,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f15])).
% 1.57/0.59  fof(f15,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f11,plain,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f6])).
% 1.57/0.59  fof(f6,axiom,(
% 1.57/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.57/0.59  fof(f41,plain,(
% 1.57/0.59    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 1.57/0.59    inference(definition_unfolding,[],[f26,f28,f28])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 1.57/0.59    inference(cnf_transformation,[],[f14])).
% 1.57/0.59  fof(f14,plain,(
% 1.57/0.59    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 1.57/0.59  fof(f13,plain,(
% 1.57/0.59    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f9,plain,(
% 1.57/0.59    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f8])).
% 1.57/0.59  fof(f8,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 1.57/0.59    inference(negated_conjecture,[],[f7])).
% 1.57/0.59  fof(f7,conjecture,(
% 1.57/0.59    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 1.57/0.59  fof(f145,plain,(
% 1.57/0.59    ( ! [X2] : (~r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),X2) | r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),X2)) )),
% 1.57/0.59    inference(resolution,[],[f72,f32])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 1.57/0.59  fof(f19,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f18,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(rectify,[],[f17])).
% 1.57/0.59  fof(f17,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(nnf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,plain,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f2])).
% 1.57/0.59  fof(f2,axiom,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.59  fof(f72,plain,(
% 1.57/0.59    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))))),
% 1.57/0.59    inference(resolution,[],[f59,f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f59,plain,(
% 1.57/0.59    ~r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 1.57/0.59    inference(resolution,[],[f41,f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f16])).
% 1.57/0.59  fof(f184,plain,(
% 1.57/0.59    spl6_3),
% 1.57/0.59    inference(avatar_split_clause,[],[f178,f130])).
% 1.57/0.59  fof(f130,plain,(
% 1.57/0.59    spl6_3 <=> r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.57/0.59  fof(f178,plain,(
% 1.57/0.59    r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0))),
% 1.57/0.59    inference(resolution,[],[f101,f72])).
% 1.57/0.59  fof(f101,plain,(
% 1.57/0.59    ( ! [X0] : (~r2_hidden(X0,sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))) | r2_hidden(X0,k3_tarski(sK0))) )),
% 1.57/0.59    inference(resolution,[],[f90,f32])).
% 1.57/0.59  fof(f90,plain,(
% 1.57/0.59    r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0))),
% 1.57/0.59    inference(resolution,[],[f62,f29])).
% 1.57/0.59  fof(f62,plain,(
% 1.57/0.59    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0)),
% 1.57/0.59    inference(resolution,[],[f58,f51])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.59    inference(equality_resolution,[],[f48])).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.57/0.59    inference(definition_unfolding,[],[f35,f28])).
% 1.57/0.59  fof(f35,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.59    inference(cnf_transformation,[],[f25])).
% 1.57/0.59  fof(f137,plain,(
% 1.57/0.59    ~spl6_3 | ~spl6_4),
% 1.57/0.59    inference(avatar_split_clause,[],[f125,f134,f130])).
% 1.57/0.59  fof(f125,plain,(
% 1.57/0.59    ~r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK1)) | ~r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k3_tarski(sK0))),
% 1.57/0.59    inference(resolution,[],[f73,f49])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.57/0.59    inference(equality_resolution,[],[f46])).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.57/0.59    inference(definition_unfolding,[],[f37,f28])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.59    inference(cnf_transformation,[],[f25])).
% 1.57/0.59  fof(f73,plain,(
% 1.57/0.59    ~r2_hidden(sK3(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 1.57/0.59    inference(resolution,[],[f59,f34])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  % SZS output end Proof for theBenchmark
% 1.57/0.59  % (23175)------------------------------
% 1.57/0.59  % (23175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (23175)Termination reason: Refutation
% 1.57/0.59  
% 1.57/0.59  % (23175)Memory used [KB]: 6396
% 1.57/0.59  % (23175)Time elapsed: 0.171 s
% 1.57/0.59  % (23175)------------------------------
% 1.57/0.59  % (23175)------------------------------
% 1.57/0.59  % (23156)Success in time 0.218 s
%------------------------------------------------------------------------------
