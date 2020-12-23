%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 2.57s
% Output     : Refutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 412 expanded)
%              Number of leaves         :   13 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          :  231 (1247 expanded)
%              Number of equality atoms :   33 ( 145 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2129,f291])).

fof(f291,plain,(
    r2_hidden(sK6(sK0),sK4) ),
    inference(resolution,[],[f288,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
      & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK6(sK0),X1) ) ),
    inference(superposition,[],[f50,f286])).

fof(f286,plain,(
    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f2129,plain,(
    ~ r2_hidden(sK6(sK0),sK4) ),
    inference(resolution,[],[f1165,f1748])).

fof(f1748,plain,(
    ~ r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4)))) ),
    inference(subsumption_resolution,[],[f1569,f1724])).

fof(f1724,plain,(
    r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3)))) ),
    inference(resolution,[],[f1708,f657])).

fof(f657,plain,(
    ! [X1] : ~ r2_hidden(sK5(sK0),k5_xboole_0(X1,k5_xboole_0(sK1,k5_xboole_0(sK3,X1)))) ),
    inference(resolution,[],[f400,f428])).

fof(f428,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0),k5_xboole_0(sK3,X0))
      | ~ r2_hidden(sK5(sK0),X0) ) ),
    inference(resolution,[],[f420,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f420,plain,(
    ! [X2] : r2_hidden(sK5(sK0),k5_xboole_0(X2,k5_xboole_0(sK3,X2))) ),
    inference(resolution,[],[f301,f150])).

fof(f150,plain,(
    ! [X2,X3,X1] : ~ r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ),
    inference(superposition,[],[f107,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f107,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f54,f91])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(backward_demodulation,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f301,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0),k5_xboole_0(sK3,X1))
      | r2_hidden(sK5(sK0),X1) ) ),
    inference(resolution,[],[f297,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f297,plain,(
    r2_hidden(sK5(sK0),sK3) ),
    inference(resolution,[],[f289,f42])).

fof(f289,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK5(sK0),X2) ) ),
    inference(superposition,[],[f49,f286])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f400,plain,(
    ! [X0,X1] : r2_hidden(sK5(sK0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,k5_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f385,f68])).

fof(f385,plain,(
    ! [X2] : r2_hidden(sK5(sK0),k5_xboole_0(X2,k5_xboole_0(sK1,X2))) ),
    inference(resolution,[],[f299,f150])).

fof(f299,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0),k5_xboole_0(sK1,X1))
      | r2_hidden(sK5(sK0),X1) ) ),
    inference(resolution,[],[f296,f55])).

fof(f296,plain,(
    r2_hidden(sK5(sK0),sK1) ),
    inference(resolution,[],[f289,f41])).

fof(f1708,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0),k5_xboole_0(k2_xboole_0(sK1,sK3),X1))
      | r2_hidden(sK5(sK0),X1) ) ),
    inference(resolution,[],[f1706,f55])).

fof(f1706,plain,(
    r2_hidden(sK5(sK0),k2_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f1701,f297])).

fof(f1701,plain,
    ( ~ r2_hidden(sK5(sK0),sK3)
    | r2_hidden(sK5(sK0),k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f1691,f301])).

fof(f1691,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0),k5_xboole_0(X0,k2_xboole_0(sK1,X0)))
      | ~ r2_hidden(sK5(sK0),X0) ) ),
    inference(resolution,[],[f1163,f393])).

fof(f393,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0),k5_xboole_0(sK1,X0))
      | ~ r2_hidden(sK5(sK0),X0) ) ),
    inference(resolution,[],[f385,f54])).

fof(f1163,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(X2,k2_xboole_0(sK1,X2))))
      | ~ r2_hidden(sK5(sK0),X2) ) ),
    inference(resolution,[],[f96,f299])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(backward_demodulation,[],[f83,f68])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1569,plain,
    ( ~ r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4))))
    | ~ r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3)))) ),
    inference(resolution,[],[f103,f931])).

fof(f931,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK6(sK0),X1)
      | ~ r2_hidden(sK5(sK0),X0) ) ),
    inference(superposition,[],[f51,f286])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4))))) ),
    inference(forward_demodulation,[],[f102,f68])).

fof(f102,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))),k5_xboole_0(k5_xboole_0(sK2,sK4),k2_xboole_0(sK2,sK4)))) ),
    inference(backward_demodulation,[],[f70,f68])).

fof(f70,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)),k5_xboole_0(k5_xboole_0(sK2,sK4),k2_xboole_0(sK2,sK4)))) ),
    inference(definition_unfolding,[],[f43,f46,f46])).

fof(f43,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1165,plain,(
    ! [X4] :
      ( r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(X4,k2_xboole_0(sK2,X4))))
      | ~ r2_hidden(sK6(sK0),X4) ) ),
    inference(resolution,[],[f96,f293])).

fof(f293,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK0),k5_xboole_0(sK2,X1))
      | r2_hidden(sK6(sK0),X1) ) ),
    inference(resolution,[],[f290,f55])).

fof(f290,plain,(
    r2_hidden(sK6(sK0),sK2) ),
    inference(resolution,[],[f288,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15984)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (16002)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (15994)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15992)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (15986)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (16001)Refutation not found, incomplete strategy% (16001)------------------------------
% 0.21/0.53  % (16001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16001)Memory used [KB]: 10746
% 0.21/0.53  % (16001)Time elapsed: 0.116 s
% 0.21/0.53  % (16001)------------------------------
% 0.21/0.53  % (16001)------------------------------
% 0.21/0.54  % (16004)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15983)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (15985)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (15982)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (15993)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (15981)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (16008)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (15981)Refutation not found, incomplete strategy% (15981)------------------------------
% 0.21/0.55  % (15981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15981)Memory used [KB]: 10746
% 0.21/0.55  % (15981)Time elapsed: 0.132 s
% 0.21/0.55  % (15981)------------------------------
% 0.21/0.55  % (15981)------------------------------
% 0.21/0.55  % (16005)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (16000)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (16006)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (15980)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (15989)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (15990)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (15991)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (15997)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (15998)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (15996)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (15996)Refutation not found, incomplete strategy% (15996)------------------------------
% 0.21/0.57  % (15996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15996)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15996)Memory used [KB]: 10618
% 0.21/0.57  % (15996)Time elapsed: 0.153 s
% 0.21/0.57  % (15996)------------------------------
% 0.21/0.57  % (15996)------------------------------
% 0.21/0.58  % (15979)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (15987)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (15999)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.59  % (16007)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.59  % (16003)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.59  % (15987)Refutation not found, incomplete strategy% (15987)------------------------------
% 0.21/0.59  % (15987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (15995)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (15988)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.61  % (15987)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (15987)Memory used [KB]: 10746
% 0.21/0.61  % (15987)Time elapsed: 0.181 s
% 0.21/0.61  % (15987)------------------------------
% 0.21/0.61  % (15987)------------------------------
% 2.25/0.68  % (16012)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.25/0.70  % (16013)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.57/0.72  % (15984)Refutation found. Thanks to Tanya!
% 2.57/0.72  % SZS status Theorem for theBenchmark
% 2.57/0.72  % SZS output start Proof for theBenchmark
% 2.57/0.72  fof(f2137,plain,(
% 2.57/0.72    $false),
% 2.57/0.72    inference(subsumption_resolution,[],[f2129,f291])).
% 2.57/0.72  fof(f291,plain,(
% 2.57/0.72    r2_hidden(sK6(sK0),sK4)),
% 2.57/0.72    inference(resolution,[],[f288,f42])).
% 2.57/0.72  fof(f42,plain,(
% 2.57/0.72    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 2.57/0.72    inference(cnf_transformation,[],[f30])).
% 2.57/0.72  fof(f30,plain,(
% 2.57/0.72    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 2.57/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f29])).
% 2.57/0.72  fof(f29,plain,(
% 2.57/0.72    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => (~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 2.57/0.72    introduced(choice_axiom,[])).
% 2.57/0.72  fof(f26,plain,(
% 2.57/0.72    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.57/0.72    inference(flattening,[],[f25])).
% 2.57/0.72  fof(f25,plain,(
% 2.57/0.72    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 2.57/0.72    inference(ennf_transformation,[],[f22])).
% 2.57/0.72  fof(f22,negated_conjecture,(
% 2.57/0.72    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 2.57/0.72    inference(negated_conjecture,[],[f21])).
% 2.57/0.72  fof(f21,conjecture,(
% 2.57/0.72    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).
% 2.57/0.72  fof(f288,plain,(
% 2.57/0.72    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(sK0),X1)) )),
% 2.57/0.72    inference(superposition,[],[f50,f286])).
% 2.57/0.72  fof(f286,plain,(
% 2.57/0.72    sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 2.57/0.72    inference(resolution,[],[f52,f41])).
% 2.57/0.72  fof(f41,plain,(
% 2.57/0.72    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 2.57/0.72    inference(cnf_transformation,[],[f30])).
% 2.57/0.72  fof(f52,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 2.57/0.72    inference(cnf_transformation,[],[f34])).
% 2.57/0.72  fof(f34,plain,(
% 2.57/0.72    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.57/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f33])).
% 2.57/0.72  fof(f33,plain,(
% 2.57/0.72    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 2.57/0.72    introduced(choice_axiom,[])).
% 2.57/0.72  fof(f27,plain,(
% 2.57/0.72    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.57/0.72    inference(ennf_transformation,[],[f15])).
% 2.57/0.72  fof(f15,axiom,(
% 2.57/0.72    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.57/0.72  fof(f50,plain,(
% 2.57/0.72    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f32])).
% 2.57/0.72  fof(f32,plain,(
% 2.57/0.72    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.57/0.72    inference(flattening,[],[f31])).
% 2.57/0.72  fof(f31,plain,(
% 2.57/0.72    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.57/0.72    inference(nnf_transformation,[],[f17])).
% 2.57/0.72  fof(f17,axiom,(
% 2.57/0.72    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.57/0.72  fof(f2129,plain,(
% 2.57/0.72    ~r2_hidden(sK6(sK0),sK4)),
% 2.57/0.72    inference(resolution,[],[f1165,f1748])).
% 2.57/0.72  fof(f1748,plain,(
% 2.57/0.72    ~r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4))))),
% 2.57/0.72    inference(subsumption_resolution,[],[f1569,f1724])).
% 2.57/0.72  fof(f1724,plain,(
% 2.57/0.72    r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))))),
% 2.57/0.72    inference(resolution,[],[f1708,f657])).
% 2.57/0.72  fof(f657,plain,(
% 2.57/0.72    ( ! [X1] : (~r2_hidden(sK5(sK0),k5_xboole_0(X1,k5_xboole_0(sK1,k5_xboole_0(sK3,X1))))) )),
% 2.57/0.72    inference(resolution,[],[f400,f428])).
% 2.57/0.72  fof(f428,plain,(
% 2.57/0.72    ( ! [X0] : (~r2_hidden(sK5(sK0),k5_xboole_0(sK3,X0)) | ~r2_hidden(sK5(sK0),X0)) )),
% 2.57/0.72    inference(resolution,[],[f420,f54])).
% 2.57/0.72  fof(f54,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f35])).
% 2.57/0.72  fof(f35,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.57/0.72    inference(nnf_transformation,[],[f28])).
% 2.57/0.72  fof(f28,plain,(
% 2.57/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.57/0.72    inference(ennf_transformation,[],[f4])).
% 2.57/0.72  fof(f4,axiom,(
% 2.57/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.57/0.72  fof(f420,plain,(
% 2.57/0.72    ( ! [X2] : (r2_hidden(sK5(sK0),k5_xboole_0(X2,k5_xboole_0(sK3,X2)))) )),
% 2.57/0.72    inference(resolution,[],[f301,f150])).
% 2.57/0.72  fof(f150,plain,(
% 2.57/0.72    ( ! [X2,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))))) )),
% 2.57/0.72    inference(superposition,[],[f107,f68])).
% 2.57/0.72  fof(f68,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.57/0.72    inference(cnf_transformation,[],[f6])).
% 2.57/0.72  fof(f6,axiom,(
% 2.57/0.72    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.57/0.72  fof(f107,plain,(
% 2.57/0.72    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 2.57/0.72    inference(subsumption_resolution,[],[f106,f53])).
% 2.57/0.72  fof(f53,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f35])).
% 2.57/0.72  fof(f106,plain,(
% 2.57/0.72    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 2.57/0.72    inference(duplicate_literal_removal,[],[f105])).
% 2.57/0.72  fof(f105,plain,(
% 2.57/0.72    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 2.57/0.72    inference(superposition,[],[f54,f91])).
% 2.57/0.72  fof(f91,plain,(
% 2.57/0.72    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.57/0.72    inference(backward_demodulation,[],[f73,f67])).
% 2.57/0.72  fof(f67,plain,(
% 2.57/0.72    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.57/0.72    inference(cnf_transformation,[],[f24])).
% 2.57/0.72  fof(f24,plain,(
% 2.57/0.72    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.57/0.72    inference(rectify,[],[f2])).
% 2.57/0.72  fof(f2,axiom,(
% 2.57/0.72    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.57/0.72  fof(f73,plain,(
% 2.57/0.72    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 2.57/0.72    inference(definition_unfolding,[],[f48,f46])).
% 2.57/0.72  fof(f46,plain,(
% 2.57/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.57/0.72    inference(cnf_transformation,[],[f8])).
% 2.57/0.72  fof(f8,axiom,(
% 2.57/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.57/0.72  fof(f48,plain,(
% 2.57/0.72    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.57/0.72    inference(cnf_transformation,[],[f23])).
% 2.57/0.72  fof(f23,plain,(
% 2.57/0.72    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.57/0.72    inference(rectify,[],[f3])).
% 2.57/0.72  fof(f3,axiom,(
% 2.57/0.72    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.57/0.72  fof(f301,plain,(
% 2.57/0.72    ( ! [X1] : (r2_hidden(sK5(sK0),k5_xboole_0(sK3,X1)) | r2_hidden(sK5(sK0),X1)) )),
% 2.57/0.72    inference(resolution,[],[f297,f55])).
% 2.57/0.72  fof(f55,plain,(
% 2.57/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.57/0.72    inference(cnf_transformation,[],[f35])).
% 2.57/0.72  fof(f297,plain,(
% 2.57/0.72    r2_hidden(sK5(sK0),sK3)),
% 2.57/0.72    inference(resolution,[],[f289,f42])).
% 2.57/0.72  fof(f289,plain,(
% 2.57/0.72    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(sK5(sK0),X2)) )),
% 2.57/0.72    inference(superposition,[],[f49,f286])).
% 2.57/0.72  fof(f49,plain,(
% 2.57/0.72    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f32])).
% 2.57/0.72  fof(f400,plain,(
% 2.57/0.72    ( ! [X0,X1] : (r2_hidden(sK5(sK0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,k5_xboole_0(X0,X1)))))) )),
% 2.57/0.72    inference(superposition,[],[f385,f68])).
% 2.57/0.72  fof(f385,plain,(
% 2.57/0.72    ( ! [X2] : (r2_hidden(sK5(sK0),k5_xboole_0(X2,k5_xboole_0(sK1,X2)))) )),
% 2.57/0.72    inference(resolution,[],[f299,f150])).
% 2.57/0.72  fof(f299,plain,(
% 2.57/0.72    ( ! [X1] : (r2_hidden(sK5(sK0),k5_xboole_0(sK1,X1)) | r2_hidden(sK5(sK0),X1)) )),
% 2.57/0.72    inference(resolution,[],[f296,f55])).
% 2.57/0.72  fof(f296,plain,(
% 2.57/0.72    r2_hidden(sK5(sK0),sK1)),
% 2.57/0.72    inference(resolution,[],[f289,f41])).
% 2.57/0.72  fof(f1708,plain,(
% 2.57/0.72    ( ! [X1] : (r2_hidden(sK5(sK0),k5_xboole_0(k2_xboole_0(sK1,sK3),X1)) | r2_hidden(sK5(sK0),X1)) )),
% 2.57/0.72    inference(resolution,[],[f1706,f55])).
% 2.57/0.72  fof(f1706,plain,(
% 2.57/0.72    r2_hidden(sK5(sK0),k2_xboole_0(sK1,sK3))),
% 2.57/0.72    inference(subsumption_resolution,[],[f1701,f297])).
% 2.57/0.72  fof(f1701,plain,(
% 2.57/0.72    ~r2_hidden(sK5(sK0),sK3) | r2_hidden(sK5(sK0),k2_xboole_0(sK1,sK3))),
% 2.57/0.72    inference(resolution,[],[f1691,f301])).
% 2.57/0.72  fof(f1691,plain,(
% 2.57/0.72    ( ! [X0] : (~r2_hidden(sK5(sK0),k5_xboole_0(X0,k2_xboole_0(sK1,X0))) | ~r2_hidden(sK5(sK0),X0)) )),
% 2.57/0.72    inference(resolution,[],[f1163,f393])).
% 2.57/0.72  fof(f393,plain,(
% 2.57/0.72    ( ! [X0] : (~r2_hidden(sK5(sK0),k5_xboole_0(sK1,X0)) | ~r2_hidden(sK5(sK0),X0)) )),
% 2.57/0.72    inference(resolution,[],[f385,f54])).
% 2.57/0.72  fof(f1163,plain,(
% 2.57/0.72    ( ! [X2] : (r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(X2,k2_xboole_0(sK1,X2)))) | ~r2_hidden(sK5(sK0),X2)) )),
% 2.57/0.72    inference(resolution,[],[f96,f299])).
% 2.57/0.72  fof(f96,plain,(
% 2.57/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) | ~r2_hidden(X4,X1)) )),
% 2.57/0.72    inference(backward_demodulation,[],[f83,f68])).
% 2.57/0.72  fof(f83,plain,(
% 2.57/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 2.57/0.72    inference(equality_resolution,[],[f78])).
% 2.57/0.72  fof(f78,plain,(
% 2.57/0.72    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 2.57/0.72    inference(definition_unfolding,[],[f58,f69])).
% 2.57/0.72  fof(f69,plain,(
% 2.57/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 2.57/0.72    inference(definition_unfolding,[],[f47,f46])).
% 2.57/0.72  fof(f47,plain,(
% 2.57/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.57/0.72    inference(cnf_transformation,[],[f5])).
% 2.57/0.72  fof(f5,axiom,(
% 2.57/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.57/0.72  fof(f58,plain,(
% 2.57/0.72    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.57/0.72    inference(cnf_transformation,[],[f40])).
% 2.57/0.72  fof(f40,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.57/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 2.57/0.72  fof(f39,plain,(
% 2.57/0.72    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.57/0.72    introduced(choice_axiom,[])).
% 2.57/0.72  fof(f38,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.57/0.72    inference(rectify,[],[f37])).
% 2.57/0.72  fof(f37,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.57/0.72    inference(flattening,[],[f36])).
% 2.57/0.72  fof(f36,plain,(
% 2.57/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.57/0.72    inference(nnf_transformation,[],[f1])).
% 2.57/0.72  fof(f1,axiom,(
% 2.57/0.72    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.57/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.57/0.72  fof(f1569,plain,(
% 2.57/0.72    ~r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4)))) | ~r2_hidden(sK5(sK0),k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))))),
% 2.57/0.72    inference(resolution,[],[f103,f931])).
% 2.57/0.72  fof(f931,plain,(
% 2.57/0.72    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK6(sK0),X1) | ~r2_hidden(sK5(sK0),X0)) )),
% 2.57/0.72    inference(superposition,[],[f51,f286])).
% 2.57/0.72  fof(f51,plain,(
% 2.57/0.72    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.57/0.72    inference(cnf_transformation,[],[f32])).
% 2.57/0.72  fof(f103,plain,(
% 2.57/0.72    ~r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))),k5_xboole_0(sK2,k5_xboole_0(sK4,k2_xboole_0(sK2,sK4)))))),
% 2.57/0.72    inference(forward_demodulation,[],[f102,f68])).
% 2.57/0.72  fof(f102,plain,(
% 2.57/0.72    ~r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK3,k2_xboole_0(sK1,sK3))),k5_xboole_0(k5_xboole_0(sK2,sK4),k2_xboole_0(sK2,sK4))))),
% 2.57/0.72    inference(backward_demodulation,[],[f70,f68])).
% 2.57/0.72  fof(f70,plain,(
% 2.57/0.72    ~r2_hidden(sK0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)),k5_xboole_0(k5_xboole_0(sK2,sK4),k2_xboole_0(sK2,sK4))))),
% 2.57/0.72    inference(definition_unfolding,[],[f43,f46,f46])).
% 2.57/0.72  fof(f43,plain,(
% 2.57/0.72    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))),
% 2.57/0.72    inference(cnf_transformation,[],[f30])).
% 2.57/0.72  fof(f1165,plain,(
% 2.57/0.72    ( ! [X4] : (r2_hidden(sK6(sK0),k5_xboole_0(sK2,k5_xboole_0(X4,k2_xboole_0(sK2,X4)))) | ~r2_hidden(sK6(sK0),X4)) )),
% 2.57/0.72    inference(resolution,[],[f96,f293])).
% 2.57/0.72  fof(f293,plain,(
% 2.57/0.72    ( ! [X1] : (r2_hidden(sK6(sK0),k5_xboole_0(sK2,X1)) | r2_hidden(sK6(sK0),X1)) )),
% 2.57/0.72    inference(resolution,[],[f290,f55])).
% 2.57/0.72  fof(f290,plain,(
% 2.57/0.72    r2_hidden(sK6(sK0),sK2)),
% 2.57/0.72    inference(resolution,[],[f288,f41])).
% 2.57/0.72  % SZS output end Proof for theBenchmark
% 2.57/0.72  % (15984)------------------------------
% 2.57/0.72  % (15984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.72  % (15984)Termination reason: Refutation
% 2.57/0.72  
% 2.57/0.72  % (15984)Memory used [KB]: 8059
% 2.57/0.72  % (15984)Time elapsed: 0.294 s
% 2.57/0.72  % (15984)------------------------------
% 2.57/0.72  % (15984)------------------------------
% 2.57/0.73  % (15978)Success in time 0.359 s
%------------------------------------------------------------------------------
