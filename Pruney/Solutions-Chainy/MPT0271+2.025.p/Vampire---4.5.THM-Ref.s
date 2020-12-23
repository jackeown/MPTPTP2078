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
% DateTime   : Thu Dec  3 12:41:09 EST 2020

% Result     : Theorem 13.94s
% Output     : Refutation 13.94s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 608 expanded)
%              Number of leaves         :   16 ( 185 expanded)
%              Depth                    :   22
%              Number of atoms          :  280 (1655 expanded)
%              Number of equality atoms :  109 ( 692 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9625,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9596,f352])).

fof(f352,plain,(
    r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f274,f93])).

fof(f93,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f274,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(X12,sK1)
      | r2_hidden(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f265,f177])).

fof(f177,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f170,f98])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f55,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,X0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f168,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f168,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f167,f132])).

fof(f132,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f119,f98])).

fof(f119,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f54,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f167,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f90,f54])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f265,plain,(
    ! [X12] :
      ( r2_hidden(X12,k1_xboole_0)
      | r2_hidden(X12,sK1)
      | ~ r2_hidden(X12,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(sK0,sK1) ) ),
    inference(superposition,[],[f256,f151])).

fof(f151,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f150,f132])).

fof(f150,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f77,f54])).

fof(f77,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f72,f74])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f256,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f255,f132])).

fof(f255,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f89,f54])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9596,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f866,f9594])).

fof(f9594,plain,(
    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f9591])).

fof(f9591,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    inference(resolution,[],[f916,f177])).

fof(f916,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1)
      | k1_xboole_0 != X1
      | sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1) ) ),
    inference(resolution,[],[f363,f94])).

fof(f94,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f363,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 != X0
      | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f357,f319])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f318,f132])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f80,f54])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f357,plain,(
    k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(subsumption_resolution,[],[f157,f352])).

fof(f157,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f135,f132])).

fof(f135,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f76,f54])).

fof(f76,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f72,f74])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f866,plain,(
    ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    inference(trivial_inequality_removal,[],[f863])).

fof(f863,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution,[],[f364,f177])).

fof(f364,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1)
      | ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),sK1)
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f357,f276])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f275,f132])).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f79,f54])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (22189)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (22205)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22205)Refutation not found, incomplete strategy% (22205)------------------------------
% 0.21/0.51  % (22205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22205)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22205)Memory used [KB]: 1663
% 0.21/0.51  % (22205)Time elapsed: 0.102 s
% 0.21/0.51  % (22205)------------------------------
% 0.21/0.51  % (22205)------------------------------
% 0.21/0.51  % (22198)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (22185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (22177)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22184)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (22182)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22176)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (22178)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (22190)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (22190)Refutation not found, incomplete strategy% (22190)------------------------------
% 0.21/0.54  % (22190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22190)Memory used [KB]: 1663
% 0.21/0.54  % (22190)Time elapsed: 0.083 s
% 0.21/0.54  % (22190)------------------------------
% 0.21/0.54  % (22190)------------------------------
% 0.21/0.54  % (22188)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (22180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (22181)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (22197)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (22200)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (22203)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (22204)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (22179)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (22192)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (22192)Refutation not found, incomplete strategy% (22192)------------------------------
% 0.21/0.55  % (22192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22192)Memory used [KB]: 10618
% 0.21/0.55  % (22192)Time elapsed: 0.137 s
% 0.21/0.55  % (22192)------------------------------
% 0.21/0.55  % (22192)------------------------------
% 0.21/0.55  % (22194)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (22199)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (22202)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22201)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (22195)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (22186)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (22183)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (22196)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (22191)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (22193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (22187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (22193)Refutation not found, incomplete strategy% (22193)------------------------------
% 0.21/0.56  % (22193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22193)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22193)Memory used [KB]: 1791
% 0.21/0.56  % (22193)Time elapsed: 0.149 s
% 0.21/0.56  % (22193)------------------------------
% 0.21/0.56  % (22193)------------------------------
% 0.21/0.56  % (22187)Refutation not found, incomplete strategy% (22187)------------------------------
% 0.21/0.56  % (22187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22187)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22187)Memory used [KB]: 6268
% 0.21/0.56  % (22187)Time elapsed: 0.149 s
% 0.21/0.56  % (22187)------------------------------
% 0.21/0.56  % (22187)------------------------------
% 2.07/0.63  % (22206)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.67  % (22207)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.69  % (22179)Refutation not found, incomplete strategy% (22179)------------------------------
% 2.08/0.69  % (22179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.69  % (22179)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.69  
% 2.08/0.69  % (22179)Memory used [KB]: 6140
% 2.08/0.69  % (22179)Time elapsed: 0.275 s
% 2.08/0.69  % (22179)------------------------------
% 2.08/0.69  % (22179)------------------------------
% 2.08/0.70  % (22210)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.64/0.70  % (22209)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.64/0.71  % (22208)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.16/0.82  % (22211)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.16/0.82  % (22178)Time limit reached!
% 3.16/0.82  % (22178)------------------------------
% 3.16/0.82  % (22178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.82  % (22178)Termination reason: Time limit
% 3.16/0.82  
% 3.16/0.82  % (22178)Memory used [KB]: 6780
% 3.16/0.82  % (22178)Time elapsed: 0.405 s
% 3.16/0.82  % (22178)------------------------------
% 3.16/0.82  % (22178)------------------------------
% 3.16/0.85  % (22200)Time limit reached!
% 3.16/0.85  % (22200)------------------------------
% 3.16/0.85  % (22200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.85  % (22200)Termination reason: Time limit
% 3.16/0.85  
% 3.16/0.85  % (22200)Memory used [KB]: 13176
% 3.16/0.85  % (22200)Time elapsed: 0.436 s
% 3.16/0.85  % (22200)------------------------------
% 3.16/0.85  % (22200)------------------------------
% 4.32/0.95  % (22212)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.32/0.97  % (22182)Time limit reached!
% 4.32/0.97  % (22182)------------------------------
% 4.32/0.97  % (22182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.97  % (22182)Termination reason: Time limit
% 4.32/0.97  % (22182)Termination phase: Saturation
% 4.32/0.97  
% 4.32/0.97  % (22182)Memory used [KB]: 15991
% 4.32/0.97  % (22182)Time elapsed: 0.500 s
% 4.32/0.97  % (22182)------------------------------
% 4.32/0.97  % (22182)------------------------------
% 4.32/0.98  % (22213)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.87/1.01  % (22183)Time limit reached!
% 4.87/1.01  % (22183)------------------------------
% 4.87/1.01  % (22183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.01  % (22183)Termination reason: Time limit
% 4.87/1.01  % (22183)Termination phase: Saturation
% 4.87/1.01  
% 4.87/1.01  % (22183)Memory used [KB]: 6908
% 4.87/1.01  % (22183)Time elapsed: 0.600 s
% 4.87/1.01  % (22183)------------------------------
% 4.87/1.01  % (22183)------------------------------
% 5.36/1.12  % (22214)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.36/1.14  % (22215)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 5.36/1.14  % (22215)Refutation not found, incomplete strategy% (22215)------------------------------
% 5.36/1.14  % (22215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.36/1.14  % (22215)Termination reason: Refutation not found, incomplete strategy
% 5.36/1.14  
% 5.36/1.14  % (22215)Memory used [KB]: 10746
% 5.36/1.14  % (22215)Time elapsed: 0.116 s
% 5.36/1.14  % (22215)------------------------------
% 5.36/1.14  % (22215)------------------------------
% 6.61/1.22  % (22177)Time limit reached!
% 6.61/1.22  % (22177)------------------------------
% 6.61/1.22  % (22177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.61/1.22  % (22177)Termination reason: Time limit
% 6.61/1.22  
% 6.61/1.22  % (22177)Memory used [KB]: 3454
% 6.61/1.22  % (22177)Time elapsed: 0.814 s
% 6.61/1.22  % (22177)------------------------------
% 6.61/1.22  % (22177)------------------------------
% 6.86/1.28  % (22216)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.86/1.31  % (22210)Refutation not found, incomplete strategy% (22210)------------------------------
% 6.86/1.31  % (22210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.86/1.31  % (22210)Termination reason: Refutation not found, incomplete strategy
% 6.86/1.31  
% 6.86/1.31  % (22210)Memory used [KB]: 19701
% 6.86/1.31  % (22210)Time elapsed: 0.710 s
% 6.86/1.31  % (22210)------------------------------
% 6.86/1.31  % (22210)------------------------------
% 7.60/1.35  % (22217)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 8.07/1.41  % (22208)Time limit reached!
% 8.07/1.41  % (22208)------------------------------
% 8.07/1.41  % (22208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.41  % (22208)Termination reason: Time limit
% 8.07/1.41  
% 8.07/1.41  % (22208)Memory used [KB]: 9978
% 8.07/1.41  % (22208)Time elapsed: 0.829 s
% 8.07/1.41  % (22208)------------------------------
% 8.07/1.41  % (22208)------------------------------
% 8.07/1.42  % (22188)Time limit reached!
% 8.07/1.42  % (22188)------------------------------
% 8.07/1.42  % (22188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.42  % (22188)Termination reason: Time limit
% 8.07/1.42  
% 8.07/1.42  % (22188)Memory used [KB]: 13304
% 8.07/1.42  % (22188)Time elapsed: 1.020 s
% 8.07/1.42  % (22188)------------------------------
% 8.07/1.42  % (22188)------------------------------
% 8.07/1.43  % (22203)Time limit reached!
% 8.07/1.43  % (22203)------------------------------
% 8.07/1.43  % (22203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.43  % (22203)Termination reason: Time limit
% 8.07/1.43  
% 8.07/1.43  % (22203)Memory used [KB]: 15095
% 8.07/1.43  % (22203)Time elapsed: 1.018 s
% 8.07/1.43  % (22203)------------------------------
% 8.07/1.43  % (22203)------------------------------
% 8.60/1.46  % (22212)Time limit reached!
% 8.60/1.46  % (22212)------------------------------
% 8.60/1.46  % (22212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.60/1.46  % (22212)Termination reason: Time limit
% 8.60/1.46  % (22212)Termination phase: Saturation
% 8.60/1.46  
% 8.60/1.46  % (22212)Memory used [KB]: 17270
% 8.60/1.46  % (22212)Time elapsed: 0.600 s
% 8.60/1.46  % (22212)------------------------------
% 8.60/1.46  % (22212)------------------------------
% 8.66/1.47  % (22218)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.11/1.54  % (22219)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.11/1.55  % (22221)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 9.11/1.56  % (22220)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 9.11/1.60  % (22222)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 9.74/1.64  % (22176)Time limit reached!
% 9.74/1.64  % (22176)------------------------------
% 9.74/1.64  % (22176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.74/1.64  % (22176)Termination reason: Time limit
% 9.74/1.64  % (22176)Termination phase: Saturation
% 9.74/1.64  
% 9.74/1.64  % (22176)Memory used [KB]: 13688
% 9.74/1.64  % (22176)Time elapsed: 1.222 s
% 9.74/1.64  % (22176)------------------------------
% 9.74/1.64  % (22176)------------------------------
% 10.09/1.74  % (22223)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 10.09/1.76  % (22181)Time limit reached!
% 10.09/1.76  % (22181)------------------------------
% 10.09/1.76  % (22181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.09/1.76  % (22181)Termination reason: Time limit
% 10.09/1.76  
% 10.09/1.76  % (22181)Memory used [KB]: 18166
% 10.09/1.76  % (22181)Time elapsed: 1.346 s
% 10.09/1.76  % (22181)------------------------------
% 10.09/1.76  % (22181)------------------------------
% 11.52/1.83  % (22219)Time limit reached!
% 11.52/1.83  % (22219)------------------------------
% 11.52/1.83  % (22219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.52/1.83  % (22219)Termination reason: Time limit
% 11.52/1.83  % (22219)Termination phase: Saturation
% 11.52/1.83  
% 11.52/1.83  % (22219)Memory used [KB]: 13048
% 11.52/1.83  % (22219)Time elapsed: 0.400 s
% 11.52/1.83  % (22219)------------------------------
% 11.52/1.83  % (22219)------------------------------
% 11.66/1.85  % (22221)Time limit reached!
% 11.66/1.85  % (22221)------------------------------
% 11.66/1.85  % (22221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.85  % (22221)Termination reason: Time limit
% 11.66/1.85  % (22221)Termination phase: Saturation
% 11.66/1.85  
% 11.66/1.85  % (22221)Memory used [KB]: 7675
% 11.66/1.85  % (22221)Time elapsed: 0.400 s
% 11.66/1.85  % (22221)------------------------------
% 11.66/1.85  % (22221)------------------------------
% 11.66/1.89  % (22224)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 12.31/1.96  % (22225)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 12.77/1.99  % (22226)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.77/2.00  % (22222)Time limit reached!
% 12.77/2.00  % (22222)------------------------------
% 12.77/2.00  % (22222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.77/2.00  % (22222)Termination reason: Time limit
% 12.77/2.00  
% 12.77/2.00  % (22222)Memory used [KB]: 12409
% 12.77/2.00  % (22222)Time elapsed: 0.516 s
% 12.77/2.00  % (22222)------------------------------
% 12.77/2.00  % (22222)------------------------------
% 13.38/2.06  % (22223)Time limit reached!
% 13.38/2.06  % (22223)------------------------------
% 13.38/2.06  % (22223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.38/2.06  % (22223)Termination reason: Time limit
% 13.38/2.06  
% 13.38/2.06  % (22223)Memory used [KB]: 10618
% 13.38/2.06  % (22223)Time elapsed: 0.410 s
% 13.38/2.06  % (22223)------------------------------
% 13.38/2.06  % (22223)------------------------------
% 13.52/2.11  % (22202)Time limit reached!
% 13.52/2.11  % (22202)------------------------------
% 13.52/2.11  % (22202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.52/2.11  % (22202)Termination reason: Time limit
% 13.52/2.11  
% 13.52/2.11  % (22202)Memory used [KB]: 19957
% 13.52/2.11  % (22202)Time elapsed: 1.698 s
% 13.52/2.11  % (22202)------------------------------
% 13.52/2.11  % (22202)------------------------------
% 13.94/2.20  % (22213)Refutation found. Thanks to Tanya!
% 13.94/2.20  % SZS status Theorem for theBenchmark
% 13.94/2.20  % SZS output start Proof for theBenchmark
% 13.94/2.20  fof(f9625,plain,(
% 13.94/2.20    $false),
% 13.94/2.20    inference(subsumption_resolution,[],[f9596,f352])).
% 13.94/2.20  fof(f352,plain,(
% 13.94/2.20    r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(duplicate_literal_removal,[],[f349])).
% 13.94/2.20  fof(f349,plain,(
% 13.94/2.20    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(resolution,[],[f274,f93])).
% 13.94/2.20  fof(f93,plain,(
% 13.94/2.20    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 13.94/2.20    inference(equality_resolution,[],[f92])).
% 13.94/2.20  fof(f92,plain,(
% 13.94/2.20    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 13.94/2.20    inference(equality_resolution,[],[f86])).
% 13.94/2.20  fof(f86,plain,(
% 13.94/2.20    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 13.94/2.20    inference(definition_unfolding,[],[f51,f74])).
% 13.94/2.20  fof(f74,plain,(
% 13.94/2.20    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 13.94/2.20    inference(definition_unfolding,[],[f58,f73])).
% 13.94/2.20  fof(f73,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 13.94/2.20    inference(definition_unfolding,[],[f66,f71])).
% 13.94/2.20  fof(f71,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f17])).
% 13.94/2.20  fof(f17,axiom,(
% 13.94/2.20    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 13.94/2.20  fof(f66,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f16])).
% 13.94/2.20  fof(f16,axiom,(
% 13.94/2.20    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 13.94/2.20  fof(f58,plain,(
% 13.94/2.20    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f15])).
% 13.94/2.20  fof(f15,axiom,(
% 13.94/2.20    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 13.94/2.20  fof(f51,plain,(
% 13.94/2.20    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 13.94/2.20    inference(cnf_transformation,[],[f39])).
% 13.94/2.20  fof(f39,plain,(
% 13.94/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 13.94/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 13.94/2.20  fof(f38,plain,(
% 13.94/2.20    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 13.94/2.20    introduced(choice_axiom,[])).
% 13.94/2.20  fof(f37,plain,(
% 13.94/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 13.94/2.20    inference(rectify,[],[f36])).
% 13.94/2.20  fof(f36,plain,(
% 13.94/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 13.94/2.20    inference(nnf_transformation,[],[f14])).
% 13.94/2.20  fof(f14,axiom,(
% 13.94/2.20    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 13.94/2.20  fof(f274,plain,(
% 13.94/2.20    ( ! [X12] : (~r2_hidden(X12,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(X12,sK1) | r2_hidden(sK0,sK1)) )),
% 13.94/2.20    inference(subsumption_resolution,[],[f265,f177])).
% 13.94/2.20  fof(f177,plain,(
% 13.94/2.20    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 13.94/2.20    inference(condensation,[],[f176])).
% 13.94/2.20  fof(f176,plain,(
% 13.94/2.20    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f170,f98])).
% 13.94/2.20  fof(f98,plain,(
% 13.94/2.20    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 13.94/2.20    inference(superposition,[],[f55,f59])).
% 13.94/2.20  fof(f59,plain,(
% 13.94/2.20    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 13.94/2.20    inference(cnf_transformation,[],[f8])).
% 13.94/2.20  fof(f8,axiom,(
% 13.94/2.20    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 13.94/2.20  fof(f55,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f1])).
% 13.94/2.20  fof(f1,axiom,(
% 13.94/2.20    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 13.94/2.20  fof(f170,plain,(
% 13.94/2.20    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,X0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 13.94/2.20    inference(superposition,[],[f168,f60])).
% 13.94/2.20  fof(f60,plain,(
% 13.94/2.20    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 13.94/2.20    inference(cnf_transformation,[],[f7])).
% 13.94/2.20  fof(f7,axiom,(
% 13.94/2.20    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 13.94/2.20  fof(f168,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f167,f132])).
% 13.94/2.20  fof(f132,plain,(
% 13.94/2.20    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 13.94/2.20    inference(forward_demodulation,[],[f119,f98])).
% 13.94/2.20  fof(f119,plain,(
% 13.94/2.20    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 13.94/2.20    inference(superposition,[],[f54,f61])).
% 13.94/2.20  fof(f61,plain,(
% 13.94/2.20    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f11])).
% 13.94/2.20  fof(f11,axiom,(
% 13.94/2.20    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 13.94/2.20  fof(f54,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 13.94/2.20    inference(cnf_transformation,[],[f10])).
% 13.94/2.20  fof(f10,axiom,(
% 13.94/2.20    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 13.94/2.20  fof(f167,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) | ~r2_hidden(X4,X1)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f90,f54])).
% 13.94/2.20  fof(f90,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 13.94/2.20    inference(equality_resolution,[],[f82])).
% 13.94/2.20  fof(f82,plain,(
% 13.94/2.20    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 13.94/2.20    inference(definition_unfolding,[],[f45,f72])).
% 13.94/2.20  fof(f72,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 13.94/2.20    inference(definition_unfolding,[],[f57,f65])).
% 13.94/2.20  fof(f65,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 13.94/2.20    inference(cnf_transformation,[],[f12])).
% 13.94/2.20  fof(f12,axiom,(
% 13.94/2.20    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 13.94/2.20  fof(f57,plain,(
% 13.94/2.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.94/2.20    inference(cnf_transformation,[],[f4])).
% 13.94/2.20  fof(f4,axiom,(
% 13.94/2.20    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 13.94/2.20  fof(f45,plain,(
% 13.94/2.20    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 13.94/2.20    inference(cnf_transformation,[],[f35])).
% 13.94/2.20  fof(f35,plain,(
% 13.94/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.94/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 13.94/2.20  fof(f34,plain,(
% 13.94/2.20    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 13.94/2.20    introduced(choice_axiom,[])).
% 13.94/2.20  fof(f33,plain,(
% 13.94/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.94/2.20    inference(rectify,[],[f32])).
% 13.94/2.20  fof(f32,plain,(
% 13.94/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.94/2.20    inference(flattening,[],[f31])).
% 13.94/2.20  fof(f31,plain,(
% 13.94/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.94/2.20    inference(nnf_transformation,[],[f2])).
% 13.94/2.20  fof(f2,axiom,(
% 13.94/2.20    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 13.94/2.20  fof(f265,plain,(
% 13.94/2.20    ( ! [X12] : (r2_hidden(X12,k1_xboole_0) | r2_hidden(X12,sK1) | ~r2_hidden(X12,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,sK1)) )),
% 13.94/2.20    inference(superposition,[],[f256,f151])).
% 13.94/2.20  fof(f151,plain,(
% 13.94/2.20    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(forward_demodulation,[],[f150,f132])).
% 13.94/2.20  fof(f150,plain,(
% 13.94/2.20    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) | r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(forward_demodulation,[],[f77,f54])).
% 13.94/2.20  fof(f77,plain,(
% 13.94/2.20    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 13.94/2.20    inference(definition_unfolding,[],[f42,f72,f74])).
% 13.94/2.20  fof(f42,plain,(
% 13.94/2.20    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 13.94/2.20    inference(cnf_transformation,[],[f30])).
% 13.94/2.20  fof(f30,plain,(
% 13.94/2.20    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 13.94/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 13.94/2.20  fof(f29,plain,(
% 13.94/2.20    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 13.94/2.20    introduced(choice_axiom,[])).
% 13.94/2.20  fof(f28,plain,(
% 13.94/2.20    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 13.94/2.20    inference(nnf_transformation,[],[f25])).
% 13.94/2.20  fof(f25,plain,(
% 13.94/2.20    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 13.94/2.20    inference(ennf_transformation,[],[f24])).
% 13.94/2.20  fof(f24,negated_conjecture,(
% 13.94/2.20    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 13.94/2.20    inference(negated_conjecture,[],[f23])).
% 13.94/2.20  fof(f23,conjecture,(
% 13.94/2.20    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 13.94/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 13.94/2.20  fof(f256,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f255,f132])).
% 13.94/2.20  fof(f255,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f89,f54])).
% 13.94/2.20  fof(f89,plain,(
% 13.94/2.20    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 13.94/2.20    inference(equality_resolution,[],[f81])).
% 13.94/2.20  fof(f81,plain,(
% 13.94/2.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 13.94/2.20    inference(definition_unfolding,[],[f46,f72])).
% 13.94/2.20  fof(f46,plain,(
% 13.94/2.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 13.94/2.20    inference(cnf_transformation,[],[f35])).
% 13.94/2.20  fof(f9596,plain,(
% 13.94/2.20    ~r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(backward_demodulation,[],[f866,f9594])).
% 13.94/2.20  fof(f9594,plain,(
% 13.94/2.20    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 13.94/2.20    inference(trivial_inequality_removal,[],[f9591])).
% 13.94/2.20  fof(f9591,plain,(
% 13.94/2.20    k1_xboole_0 != k1_xboole_0 | sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 13.94/2.20    inference(resolution,[],[f916,f177])).
% 13.94/2.20  fof(f916,plain,(
% 13.94/2.20    ( ! [X1] : (r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1) | k1_xboole_0 != X1 | sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1)) )),
% 13.94/2.20    inference(resolution,[],[f363,f94])).
% 13.94/2.20  fof(f94,plain,(
% 13.94/2.20    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 13.94/2.20    inference(equality_resolution,[],[f87])).
% 13.94/2.20  fof(f87,plain,(
% 13.94/2.20    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 13.94/2.20    inference(definition_unfolding,[],[f50,f74])).
% 13.94/2.20  fof(f50,plain,(
% 13.94/2.20    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 13.94/2.20    inference(cnf_transformation,[],[f39])).
% 13.94/2.20  fof(f363,plain,(
% 13.94/2.20    ( ! [X0] : (r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 != X0 | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),X0)) )),
% 13.94/2.20    inference(superposition,[],[f357,f319])).
% 13.94/2.20  fof(f319,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f318,f132])).
% 13.94/2.20  fof(f318,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f80,f54])).
% 13.94/2.20  fof(f80,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(definition_unfolding,[],[f47,f72])).
% 13.94/2.20  fof(f47,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f35])).
% 13.94/2.20  fof(f357,plain,(
% 13.94/2.20    k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 13.94/2.20    inference(subsumption_resolution,[],[f157,f352])).
% 13.94/2.20  fof(f157,plain,(
% 13.94/2.20    k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(forward_demodulation,[],[f135,f132])).
% 13.94/2.20  fof(f135,plain,(
% 13.94/2.20    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) | ~r2_hidden(sK0,sK1)),
% 13.94/2.20    inference(forward_demodulation,[],[f76,f54])).
% 13.94/2.20  fof(f76,plain,(
% 13.94/2.20    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 13.94/2.20    inference(definition_unfolding,[],[f43,f72,f74])).
% 13.94/2.20  fof(f43,plain,(
% 13.94/2.20    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 13.94/2.20    inference(cnf_transformation,[],[f30])).
% 13.94/2.20  fof(f866,plain,(
% 13.94/2.20    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 13.94/2.20    inference(trivial_inequality_removal,[],[f863])).
% 13.94/2.20  fof(f863,plain,(
% 13.94/2.20    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | k1_xboole_0 != k1_xboole_0),
% 13.94/2.20    inference(resolution,[],[f364,f177])).
% 13.94/2.20  fof(f364,plain,(
% 13.94/2.20    ( ! [X1] : (r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1) | ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),sK1) | k1_xboole_0 != X1) )),
% 13.94/2.20    inference(superposition,[],[f357,f276])).
% 13.94/2.20  fof(f276,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f275,f132])).
% 13.94/2.20  fof(f275,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(forward_demodulation,[],[f79,f54])).
% 13.94/2.20  fof(f79,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(definition_unfolding,[],[f48,f72])).
% 13.94/2.20  fof(f48,plain,(
% 13.94/2.20    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 13.94/2.20    inference(cnf_transformation,[],[f35])).
% 13.94/2.20  % SZS output end Proof for theBenchmark
% 13.94/2.20  % (22213)------------------------------
% 13.94/2.20  % (22213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.94/2.20  % (22213)Termination reason: Refutation
% 13.94/2.20  
% 13.94/2.20  % (22213)Memory used [KB]: 12409
% 13.94/2.20  % (22213)Time elapsed: 1.328 s
% 13.94/2.20  % (22213)------------------------------
% 13.94/2.20  % (22213)------------------------------
% 14.55/2.22  % (22196)Time limit reached!
% 14.55/2.22  % (22196)------------------------------
% 14.55/2.22  % (22196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.55/2.22  % (22196)Termination reason: Time limit
% 14.55/2.22  
% 14.55/2.22  % (22196)Memory used [KB]: 31086
% 14.55/2.22  % (22196)Time elapsed: 1.810 s
% 14.55/2.22  % (22196)------------------------------
% 14.55/2.22  % (22196)------------------------------
% 14.55/2.22  % (22175)Success in time 1.847 s
%------------------------------------------------------------------------------
