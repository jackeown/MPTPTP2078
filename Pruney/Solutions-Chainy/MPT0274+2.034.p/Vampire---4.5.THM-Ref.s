%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:25 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 451 expanded)
%              Number of leaves         :    6 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  276 (3184 expanded)
%              Number of equality atoms :  100 (1131 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f587,plain,(
    $false ),
    inference(subsumption_resolution,[],[f569,f67])).

fof(f67,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f50,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK0,sK1))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f36,f20])).

fof(f20,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f569,plain,(
    r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f263,f545])).

fof(f545,plain,(
    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f530,f100])).

fof(f100,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK0,sK1))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f36,f21])).

fof(f21,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f530,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f263,f216])).

fof(f216,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f169,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != X0
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f163,f100])).

fof(f163,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != X0
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f85,f67])).

fof(f85,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != X0
      | r2_hidden(sK0,sK2)
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) ) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f263,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f198,f169])).

fof(f198,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(equality_resolution,[],[f193])).

fof(f193,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != X2
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2) ) ),
    inference(subsumption_resolution,[],[f192,f100])).

fof(f192,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != X2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2) ) ),
    inference(subsumption_resolution,[],[f87,f67])).

fof(f87,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != X2
      | r2_hidden(sK0,sK2)
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2) ) ),
    inference(superposition,[],[f22,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (3546)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.47  % (3538)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (3539)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (3530)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (3555)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (3532)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (3552)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (3531)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (3534)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (3547)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (3544)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (3541)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (3536)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (3543)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (3533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (3540)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (3537)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (3548)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (3553)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (3550)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (3551)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (3531)Refutation not found, incomplete strategy% (3531)------------------------------
% 0.20/0.53  % (3531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3531)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3531)Memory used [KB]: 10618
% 0.20/0.53  % (3531)Time elapsed: 0.101 s
% 0.20/0.53  % (3531)------------------------------
% 0.20/0.53  % (3531)------------------------------
% 0.20/0.53  % (3545)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (3535)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (3535)Refutation not found, incomplete strategy% (3535)------------------------------
% 0.20/0.53  % (3535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3535)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3535)Memory used [KB]: 6012
% 0.20/0.53  % (3535)Time elapsed: 0.126 s
% 0.20/0.53  % (3535)------------------------------
% 0.20/0.53  % (3535)------------------------------
% 0.20/0.53  % (3542)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (3536)Refutation not found, incomplete strategy% (3536)------------------------------
% 0.20/0.54  % (3536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3554)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (3536)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3536)Memory used [KB]: 10618
% 0.20/0.54  % (3536)Time elapsed: 0.121 s
% 0.20/0.54  % (3536)------------------------------
% 0.20/0.54  % (3536)------------------------------
% 1.49/0.54  % (3549)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.61/0.57  % (3548)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  fof(f587,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(subsumption_resolution,[],[f569,f67])).
% 1.61/0.57  fof(f67,plain,(
% 1.61/0.57    ~r2_hidden(sK0,sK2)),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f60])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 1.61/0.57    inference(resolution,[],[f50,f41])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.61/0.57    inference(equality_resolution,[],[f40])).
% 1.61/0.57  fof(f40,plain,(
% 1.61/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.61/0.57    inference(equality_resolution,[],[f30])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f17,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.61/0.57    inference(rectify,[],[f16])).
% 1.61/0.57  fof(f16,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.61/0.57    inference(flattening,[],[f15])).
% 1.61/0.57  fof(f15,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.61/0.57    inference(nnf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.61/0.57  fof(f50,plain,(
% 1.61/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK0,sK1)) | ~r2_hidden(X1,sK2) | ~r2_hidden(sK0,sK2)) )),
% 1.61/0.57    inference(superposition,[],[f36,f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 1.61/0.57    inference(cnf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,plain,(
% 1.61/0.57    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 1.61/0.57  fof(f8,plain,(
% 1.61/0.57    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f7,plain,(
% 1.61/0.57    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.61/0.57    inference(flattening,[],[f6])).
% 1.61/0.57  fof(f6,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.61/0.57    inference(nnf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.61/0.57    inference(ennf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,negated_conjecture,(
% 1.61/0.57    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.61/0.57    inference(negated_conjecture,[],[f3])).
% 1.61/0.57  fof(f3,conjecture,(
% 1.61/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.61/0.57    inference(equality_resolution,[],[f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.61/0.57    inference(cnf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).
% 1.61/0.57  fof(f13,plain,(
% 1.61/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f12,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.57    inference(rectify,[],[f11])).
% 1.61/0.57  fof(f11,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.57    inference(flattening,[],[f10])).
% 1.61/0.57  fof(f10,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.57    inference(nnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.61/0.57  fof(f569,plain,(
% 1.61/0.57    r2_hidden(sK0,sK2)),
% 1.61/0.57    inference(backward_demodulation,[],[f263,f545])).
% 1.61/0.57  fof(f545,plain,(
% 1.61/0.57    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(subsumption_resolution,[],[f530,f100])).
% 1.61/0.57  fof(f100,plain,(
% 1.61/0.57    ~r2_hidden(sK1,sK2)),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f92])).
% 1.61/0.57  fof(f92,plain,(
% 1.61/0.57    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.61/0.57    inference(resolution,[],[f75,f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.61/0.57    inference(equality_resolution,[],[f38])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.61/0.57    inference(equality_resolution,[],[f31])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK0,sK1)) | ~r2_hidden(X1,sK2) | ~r2_hidden(sK1,sK2)) )),
% 1.61/0.57    inference(superposition,[],[f36,f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 1.61/0.57    inference(cnf_transformation,[],[f9])).
% 1.61/0.57  fof(f530,plain,(
% 1.61/0.57    r2_hidden(sK1,sK2) | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(superposition,[],[f263,f216])).
% 1.61/0.57  fof(f216,plain,(
% 1.61/0.57    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(resolution,[],[f169,f42])).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.61/0.57    inference(equality_resolution,[],[f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f169,plain,(
% 1.61/0.57    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f168])).
% 1.61/0.57  fof(f168,plain,(
% 1.61/0.57    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(equality_resolution,[],[f164])).
% 1.61/0.57  fof(f164,plain,(
% 1.61/0.57    ( ! [X0] : (k2_tarski(sK0,sK1) != X0 | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f163,f100])).
% 1.61/0.57  fof(f163,plain,(
% 1.61/0.57    ( ! [X0] : (k2_tarski(sK0,sK1) != X0 | r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f85,f67])).
% 1.61/0.57  fof(f85,plain,(
% 1.61/0.57    ( ! [X0] : (k2_tarski(sK0,sK1) != X0 | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) )),
% 1.61/0.57    inference(superposition,[],[f22,f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f14])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.61/0.57    inference(cnf_transformation,[],[f9])).
% 1.61/0.57  fof(f263,plain,(
% 1.61/0.57    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)),
% 1.61/0.57    inference(subsumption_resolution,[],[f198,f169])).
% 1.61/0.57  fof(f198,plain,(
% 1.61/0.57    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f197])).
% 1.61/0.57  fof(f197,plain,(
% 1.61/0.57    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.61/0.57    inference(equality_resolution,[],[f193])).
% 1.61/0.57  fof(f193,plain,(
% 1.61/0.57    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f192,f100])).
% 1.61/0.57  fof(f192,plain,(
% 1.61/0.57    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f87,f67])).
% 1.61/0.57  fof(f87,plain,(
% 1.61/0.57    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X2),X2)) )),
% 1.61/0.57    inference(superposition,[],[f22,f28])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f14])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (3548)------------------------------
% 1.61/0.57  % (3548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (3548)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (3548)Memory used [KB]: 1918
% 1.61/0.57  % (3548)Time elapsed: 0.171 s
% 1.61/0.57  % (3548)------------------------------
% 1.61/0.57  % (3548)------------------------------
% 1.61/0.57  % (3539)Refutation not found, incomplete strategy% (3539)------------------------------
% 1.61/0.57  % (3539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (3539)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (3539)Memory used [KB]: 6140
% 1.61/0.57  % (3539)Time elapsed: 0.163 s
% 1.61/0.57  % (3539)------------------------------
% 1.61/0.57  % (3539)------------------------------
% 1.61/0.57  % (3529)Success in time 0.213 s
%------------------------------------------------------------------------------
