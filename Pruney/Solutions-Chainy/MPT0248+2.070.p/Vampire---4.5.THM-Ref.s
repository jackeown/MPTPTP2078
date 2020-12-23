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
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  136 (1347 expanded)
%              Number of leaves         :   22 ( 376 expanded)
%              Depth                    :   28
%              Number of atoms          :  326 (4606 expanded)
%              Number of equality atoms :  205 (2808 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1425,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1424,f730])).

fof(f730,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f52,f729])).

fof(f729,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f51,f263,f694,f728])).

fof(f728,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f721,f293])).

fof(f293,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f263])).

fof(f53,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f721,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f230,f717])).

fof(f717,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f714])).

fof(f714,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f713,f283])).

fof(f283,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | sK0 = X6
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f92,f263])).

fof(f92,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f713,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f709,f293])).

fof(f709,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f224,f685])).

fof(f685,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f123,f502])).

fof(f502,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f431,f501])).

fof(f501,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f470,f99])).

fof(f99,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f470,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f83,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f431,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f426,f263])).

fof(f426,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f307,f61])).

fof(f307,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f65,f50])).

fof(f50,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f123,plain,(
    ! [X6,X7] : k2_xboole_0(k3_xboole_0(X6,X7),X6) = X6 ),
    inference(resolution,[],[f66,f112])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f81,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f81,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f224,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k2_xboole_0(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f181,f170])).

fof(f170,plain,(
    ! [X3] :
      ( k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f125,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f125,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | k2_xboole_0(k1_tarski(X9),X10) = X10 ) ),
    inference(resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f181,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4)) ),
    inference(resolution,[],[f157,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f157,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f70,f108])).

fof(f108,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2)) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f230,plain,(
    ! [X9] :
      ( r1_tarski(k1_tarski(sK3(X9)),X9)
      | k1_xboole_0 = X9 ) ),
    inference(superposition,[],[f60,f170])).

fof(f694,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k1_tarski(sK0),sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f681,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f681,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f113,f502])).

fof(f113,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,X2),k1_tarski(sK0)) ),
    inference(superposition,[],[f81,f50])).

fof(f263,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f257,f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f154,f78])).

fof(f154,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f60,f50])).

fof(f257,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f248])).

fof(f248,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f244,f92])).

fof(f244,plain,
    ( r2_hidden(sK3(sK1),k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f224,f50])).

fof(f51,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f1424,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1405,f55])).

fof(f1405,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f777,f1385])).

fof(f1385,plain,(
    ! [X8] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f1364,f54])).

fof(f1364,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,X8) ),
    inference(backward_demodulation,[],[f299,f1362])).

fof(f1362,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(resolution,[],[f1359,f66])).

fof(f1359,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f1355,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1355,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1354,f142])).

fof(f142,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f93,f141])).

fof(f141,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f138,f54])).

fof(f138,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f64,f58])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f93,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1354,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f1353])).

fof(f1353,plain,(
    ! [X1] :
      ( X1 != X1
      | k1_xboole_0 = k1_tarski(X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f96,f1351])).

fof(f1351,plain,(
    ! [X0] : sK5(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f1349,f142])).

fof(f1349,plain,(
    ! [X0] :
      ( sK5(X0,k1_xboole_0) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(condensation,[],[f1348])).

fof(f1348,plain,(
    ! [X8,X7] :
      ( sK5(X7,k1_xboole_0) = X8
      | sK5(X7,k1_xboole_0) = X7
      | k1_xboole_0 = k1_tarski(X7) ) ),
    inference(resolution,[],[f1341,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1341,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | X2 = X3 ) ),
    inference(resolution,[],[f1336,f78])).

fof(f1336,plain,(
    ! [X19,X18] :
      ( ~ r1_tarski(k1_tarski(X18),k1_xboole_0)
      | X18 = X19 ) ),
    inference(subsumption_resolution,[],[f1327,f142])).

fof(f1327,plain,(
    ! [X19,X18] :
      ( ~ r1_tarski(k1_tarski(X18),k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X18)
      | X18 = X19 ) ),
    inference(superposition,[],[f150,f943])).

fof(f943,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k1_tarski(X8))
      | X7 = X8 ) ),
    inference(forward_demodulation,[],[f927,f54])).

fof(f927,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f511,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f511,plain,(
    ! [X10,X9] : k3_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f501,f64])).

fof(f150,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k3_xboole_0(X6,X7))
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f69,f112])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f299,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k2_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f65,f99])).

fof(f777,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f753,f99])).

fof(f753,plain,(
    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f514,f729])).

fof(f514,plain,(
    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f501,f307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28242)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (28234)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (28217)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (28223)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (28213)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28224)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (28215)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (28214)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (28212)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (28240)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.55  % (28216)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.55  % (28241)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (28237)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  % (28228)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (28238)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (28233)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.56  % (28219)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.56  % (28220)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.56  % (28232)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.56  % (28230)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.56  % (28231)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.56  % (28227)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.56  % (28223)Refutation not found, incomplete strategy% (28223)------------------------------
% 1.34/0.56  % (28223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28223)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28223)Memory used [KB]: 10618
% 1.34/0.56  % (28223)Time elapsed: 0.118 s
% 1.34/0.56  % (28223)------------------------------
% 1.34/0.56  % (28223)------------------------------
% 1.34/0.56  % (28225)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.56  % (28236)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.56  % (28221)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.56  % (28229)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.56  % (28222)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.57  % (28222)Refutation not found, incomplete strategy% (28222)------------------------------
% 1.55/0.57  % (28222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (28222)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (28222)Memory used [KB]: 10618
% 1.55/0.57  % (28222)Time elapsed: 0.147 s
% 1.55/0.57  % (28222)------------------------------
% 1.55/0.57  % (28222)------------------------------
% 1.55/0.57  % (28239)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.58  % (28235)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.55/0.59  % (28218)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.13/0.67  % (28219)Refutation found. Thanks to Tanya!
% 2.13/0.67  % SZS status Theorem for theBenchmark
% 2.38/0.68  % SZS output start Proof for theBenchmark
% 2.38/0.68  fof(f1425,plain,(
% 2.38/0.68    $false),
% 2.38/0.68    inference(subsumption_resolution,[],[f1424,f730])).
% 2.38/0.68  fof(f730,plain,(
% 2.38/0.68    sK2 != k1_tarski(sK0)),
% 2.38/0.68    inference(subsumption_resolution,[],[f52,f729])).
% 2.38/0.68  fof(f729,plain,(
% 2.38/0.68    k1_xboole_0 = sK1),
% 2.38/0.68    inference(global_subsumption,[],[f51,f263,f694,f728])).
% 2.38/0.68  fof(f728,plain,(
% 2.38/0.68    r1_tarski(k1_tarski(sK0),sK2) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(subsumption_resolution,[],[f721,f293])).
% 2.38/0.68  fof(f293,plain,(
% 2.38/0.68    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.38/0.68    inference(trivial_inequality_removal,[],[f271])).
% 2.38/0.68  fof(f271,plain,(
% 2.38/0.68    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f53,f263])).
% 2.38/0.68  fof(f53,plain,(
% 2.38/0.68    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.38/0.68    inference(cnf_transformation,[],[f35])).
% 2.38/0.68  fof(f35,plain,(
% 2.38/0.68    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).
% 2.38/0.68  fof(f34,plain,(
% 2.38/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f30,plain,(
% 2.38/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.38/0.68    inference(ennf_transformation,[],[f27])).
% 2.38/0.68  fof(f27,negated_conjecture,(
% 2.38/0.68    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.38/0.68    inference(negated_conjecture,[],[f26])).
% 2.38/0.68  fof(f26,conjecture,(
% 2.38/0.68    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.38/0.68  fof(f721,plain,(
% 2.38/0.68    r1_tarski(k1_tarski(sK0),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f230,f717])).
% 2.38/0.68  fof(f717,plain,(
% 2.38/0.68    sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(duplicate_literal_removal,[],[f714])).
% 2.38/0.68  fof(f714,plain,(
% 2.38/0.68    k1_xboole_0 = sK1 | sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(resolution,[],[f713,f283])).
% 2.38/0.68  fof(f283,plain,(
% 2.38/0.68    ( ! [X6] : (~r2_hidden(X6,sK1) | sK0 = X6 | k1_xboole_0 = sK1) )),
% 2.38/0.68    inference(superposition,[],[f92,f263])).
% 2.38/0.68  fof(f92,plain,(
% 2.38/0.68    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.38/0.68    inference(equality_resolution,[],[f73])).
% 2.38/0.68  fof(f73,plain,(
% 2.38/0.68    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.38/0.68    inference(cnf_transformation,[],[f47])).
% 2.38/0.68  fof(f47,plain,(
% 2.38/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 2.38/0.68  fof(f46,plain,(
% 2.38/0.68    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f45,plain,(
% 2.38/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.38/0.68    inference(rectify,[],[f44])).
% 2.38/0.68  fof(f44,plain,(
% 2.38/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.38/0.68    inference(nnf_transformation,[],[f15])).
% 2.38/0.68  fof(f15,axiom,(
% 2.38/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.38/0.68  fof(f713,plain,(
% 2.38/0.68    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(subsumption_resolution,[],[f709,f293])).
% 2.38/0.68  fof(f709,plain,(
% 2.38/0.68    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f224,f685])).
% 2.38/0.68  fof(f685,plain,(
% 2.38/0.68    sK1 = k2_xboole_0(sK2,sK1) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f123,f502])).
% 2.38/0.68  fof(f502,plain,(
% 2.38/0.68    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(backward_demodulation,[],[f431,f501])).
% 2.38/0.68  fof(f501,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.38/0.68    inference(forward_demodulation,[],[f470,f99])).
% 2.38/0.68  fof(f99,plain,(
% 2.38/0.68    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.38/0.68    inference(superposition,[],[f61,f55])).
% 2.38/0.68  fof(f55,plain,(
% 2.38/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f10])).
% 2.38/0.68  fof(f10,axiom,(
% 2.38/0.68    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.38/0.68  fof(f61,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f1])).
% 2.38/0.68  fof(f1,axiom,(
% 2.38/0.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.38/0.68  fof(f470,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(superposition,[],[f83,f54])).
% 2.38/0.68  fof(f54,plain,(
% 2.38/0.68    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f13])).
% 2.38/0.68  fof(f13,axiom,(
% 2.38/0.68    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.38/0.68  fof(f83,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f12])).
% 2.38/0.68  fof(f12,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.38/0.68  fof(f431,plain,(
% 2.38/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f426,f263])).
% 2.38/0.68  fof(f426,plain,(
% 2.38/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 2.38/0.68    inference(superposition,[],[f307,f61])).
% 2.38/0.68  fof(f307,plain,(
% 2.38/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 2.38/0.68    inference(superposition,[],[f65,f50])).
% 2.38/0.68  fof(f50,plain,(
% 2.38/0.68    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.38/0.68    inference(cnf_transformation,[],[f35])).
% 2.38/0.68  fof(f65,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f14])).
% 2.38/0.68  fof(f14,axiom,(
% 2.38/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.38/0.68  fof(f123,plain,(
% 2.38/0.68    ( ! [X6,X7] : (k2_xboole_0(k3_xboole_0(X6,X7),X6) = X6) )),
% 2.38/0.68    inference(resolution,[],[f66,f112])).
% 2.38/0.68  fof(f112,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.38/0.68    inference(superposition,[],[f81,f59])).
% 2.38/0.68  fof(f59,plain,(
% 2.38/0.68    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f29])).
% 2.38/0.68  fof(f29,plain,(
% 2.38/0.68    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.68    inference(rectify,[],[f3])).
% 2.38/0.68  fof(f3,axiom,(
% 2.38/0.68    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.38/0.68  fof(f81,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f9])).
% 2.38/0.68  fof(f9,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.38/0.68  fof(f66,plain,(
% 2.38/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.38/0.68    inference(cnf_transformation,[],[f32])).
% 2.38/0.68  fof(f32,plain,(
% 2.38/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.38/0.68    inference(ennf_transformation,[],[f8])).
% 2.38/0.68  fof(f8,axiom,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.38/0.68  fof(f224,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r2_hidden(sK3(X0),k2_xboole_0(X0,X1)) | k1_xboole_0 = X0) )),
% 2.38/0.68    inference(superposition,[],[f181,f170])).
% 2.38/0.68  fof(f170,plain,(
% 2.38/0.68    ( ! [X3] : (k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3 | k1_xboole_0 = X3) )),
% 2.38/0.68    inference(resolution,[],[f125,f57])).
% 2.38/0.68  fof(f57,plain,(
% 2.38/0.68    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f37])).
% 2.38/0.68  fof(f37,plain,(
% 2.38/0.68    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f36])).
% 2.38/0.68  fof(f36,plain,(
% 2.38/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f31,plain,(
% 2.38/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.38/0.68    inference(ennf_transformation,[],[f5])).
% 2.38/0.68  fof(f5,axiom,(
% 2.38/0.68    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.38/0.68  fof(f125,plain,(
% 2.38/0.68    ( ! [X10,X9] : (~r2_hidden(X9,X10) | k2_xboole_0(k1_tarski(X9),X10) = X10) )),
% 2.38/0.68    inference(resolution,[],[f66,f78])).
% 2.38/0.68  fof(f78,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f48])).
% 2.38/0.68  fof(f48,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.38/0.68    inference(nnf_transformation,[],[f23])).
% 2.38/0.68  fof(f23,axiom,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.38/0.68  fof(f181,plain,(
% 2.38/0.68    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4))) )),
% 2.38/0.68    inference(resolution,[],[f157,f60])).
% 2.38/0.68  fof(f60,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f11])).
% 2.38/0.68  fof(f11,axiom,(
% 2.38/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.38/0.68  fof(f157,plain,(
% 2.38/0.68    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3) | r2_hidden(X2,X3)) )),
% 2.38/0.68    inference(resolution,[],[f70,f108])).
% 2.38/0.68  fof(f108,plain,(
% 2.38/0.68    ( ! [X2,X1] : (r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2))) )),
% 2.38/0.68    inference(resolution,[],[f77,f60])).
% 2.38/0.68  fof(f77,plain,(
% 2.38/0.68    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f48])).
% 2.38/0.68  fof(f70,plain,(
% 2.38/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f43])).
% 2.38/0.68  fof(f43,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 2.38/0.68  fof(f42,plain,(
% 2.38/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f41,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(rectify,[],[f40])).
% 2.38/0.68  fof(f40,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(nnf_transformation,[],[f33])).
% 2.38/0.68  fof(f33,plain,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/0.68    inference(ennf_transformation,[],[f2])).
% 2.38/0.68  fof(f2,axiom,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.38/0.68  fof(f230,plain,(
% 2.38/0.68    ( ! [X9] : (r1_tarski(k1_tarski(sK3(X9)),X9) | k1_xboole_0 = X9) )),
% 2.38/0.68    inference(superposition,[],[f60,f170])).
% 2.38/0.68  fof(f694,plain,(
% 2.38/0.68    k1_xboole_0 = sK1 | ~r1_tarski(k1_tarski(sK0),sK2) | sK2 = k1_tarski(sK0)),
% 2.38/0.68    inference(resolution,[],[f681,f69])).
% 2.38/0.68  fof(f69,plain,(
% 2.38/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.38/0.68    inference(cnf_transformation,[],[f39])).
% 2.38/0.68  fof(f39,plain,(
% 2.38/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.68    inference(flattening,[],[f38])).
% 2.38/0.68  fof(f38,plain,(
% 2.38/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.68    inference(nnf_transformation,[],[f6])).
% 2.38/0.68  fof(f6,axiom,(
% 2.38/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.38/0.68  fof(f681,plain,(
% 2.38/0.68    r1_tarski(sK2,k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f113,f502])).
% 2.38/0.68  fof(f113,plain,(
% 2.38/0.68    ( ! [X2] : (r1_tarski(k3_xboole_0(sK1,X2),k1_tarski(sK0))) )),
% 2.38/0.68    inference(superposition,[],[f81,f50])).
% 2.38/0.68  fof(f263,plain,(
% 2.38/0.68    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(resolution,[],[f257,f155])).
% 2.38/0.68  fof(f155,plain,(
% 2.38/0.68    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.38/0.68    inference(resolution,[],[f154,f78])).
% 2.38/0.68  fof(f154,plain,(
% 2.38/0.68    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.38/0.68    inference(resolution,[],[f69,f98])).
% 2.38/0.68  fof(f98,plain,(
% 2.38/0.68    r1_tarski(sK1,k1_tarski(sK0))),
% 2.38/0.68    inference(superposition,[],[f60,f50])).
% 2.38/0.68  fof(f257,plain,(
% 2.38/0.68    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(duplicate_literal_removal,[],[f256])).
% 2.38/0.68  fof(f256,plain,(
% 2.38/0.68    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f57,f248])).
% 2.38/0.68  fof(f248,plain,(
% 2.38/0.68    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(resolution,[],[f244,f92])).
% 2.38/0.68  fof(f244,plain,(
% 2.38/0.68    r2_hidden(sK3(sK1),k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.38/0.68    inference(superposition,[],[f224,f50])).
% 2.38/0.68  fof(f51,plain,(
% 2.38/0.68    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.38/0.68    inference(cnf_transformation,[],[f35])).
% 2.38/0.68  fof(f52,plain,(
% 2.38/0.68    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.38/0.68    inference(cnf_transformation,[],[f35])).
% 2.38/0.68  fof(f1424,plain,(
% 2.38/0.68    sK2 = k1_tarski(sK0)),
% 2.38/0.68    inference(forward_demodulation,[],[f1405,f55])).
% 2.38/0.68  fof(f1405,plain,(
% 2.38/0.68    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 2.38/0.68    inference(backward_demodulation,[],[f777,f1385])).
% 2.38/0.68  fof(f1385,plain,(
% 2.38/0.68    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1364,f54])).
% 2.38/0.68  fof(f1364,plain,(
% 2.38/0.68    ( ! [X8] : (k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,X8)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f299,f1362])).
% 2.38/0.68  fof(f1362,plain,(
% 2.38/0.68    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.38/0.68    inference(resolution,[],[f1359,f66])).
% 2.38/0.68  fof(f1359,plain,(
% 2.38/0.68    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.38/0.68    inference(resolution,[],[f1355,f71])).
% 2.38/0.68  fof(f71,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f43])).
% 2.38/0.68  fof(f1355,plain,(
% 2.38/0.68    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f1354,f142])).
% 2.38/0.68  fof(f142,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f93,f141])).
% 2.38/0.68  fof(f141,plain,(
% 2.38/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f138,f54])).
% 2.38/0.68  fof(f138,plain,(
% 2.38/0.68    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.38/0.68    inference(superposition,[],[f64,f58])).
% 2.38/0.68  fof(f58,plain,(
% 2.38/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f28])).
% 2.38/0.68  fof(f28,plain,(
% 2.38/0.68    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.38/0.68    inference(rectify,[],[f4])).
% 2.38/0.68  fof(f4,axiom,(
% 2.38/0.68    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.38/0.68  fof(f64,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f7])).
% 2.38/0.68  fof(f7,axiom,(
% 2.38/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.38/0.68  fof(f93,plain,(
% 2.38/0.68    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 2.38/0.68    inference(equality_resolution,[],[f79])).
% 2.38/0.68  fof(f79,plain,(
% 2.38/0.68    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f49])).
% 2.38/0.68  fof(f49,plain,(
% 2.38/0.68    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.38/0.68    inference(nnf_transformation,[],[f25])).
% 2.38/0.68  fof(f25,axiom,(
% 2.38/0.68    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.38/0.68  fof(f1354,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k1_tarski(X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.38/0.68    inference(trivial_inequality_removal,[],[f1353])).
% 2.38/0.68  fof(f1353,plain,(
% 2.38/0.68    ( ! [X1] : (X1 != X1 | k1_xboole_0 = k1_tarski(X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f96,f1351])).
% 2.38/0.68  fof(f1351,plain,(
% 2.38/0.68    ( ! [X0] : (sK5(X0,k1_xboole_0) = X0) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f1349,f142])).
% 2.38/0.68  fof(f1349,plain,(
% 2.38/0.68    ( ! [X0] : (sK5(X0,k1_xboole_0) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 2.38/0.68    inference(condensation,[],[f1348])).
% 2.38/0.68  fof(f1348,plain,(
% 2.38/0.68    ( ! [X8,X7] : (sK5(X7,k1_xboole_0) = X8 | sK5(X7,k1_xboole_0) = X7 | k1_xboole_0 = k1_tarski(X7)) )),
% 2.38/0.68    inference(resolution,[],[f1341,f75])).
% 2.38/0.68  fof(f75,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 2.38/0.68    inference(cnf_transformation,[],[f47])).
% 2.38/0.68  fof(f1341,plain,(
% 2.38/0.68    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | X2 = X3) )),
% 2.38/0.68    inference(resolution,[],[f1336,f78])).
% 2.38/0.68  fof(f1336,plain,(
% 2.38/0.68    ( ! [X19,X18] : (~r1_tarski(k1_tarski(X18),k1_xboole_0) | X18 = X19) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f1327,f142])).
% 2.38/0.68  fof(f1327,plain,(
% 2.38/0.68    ( ! [X19,X18] : (~r1_tarski(k1_tarski(X18),k1_xboole_0) | k1_xboole_0 = k1_tarski(X18) | X18 = X19) )),
% 2.38/0.68    inference(superposition,[],[f150,f943])).
% 2.38/0.68  fof(f943,plain,(
% 2.38/0.68    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) | X7 = X8) )),
% 2.38/0.68    inference(forward_demodulation,[],[f927,f54])).
% 2.38/0.68  fof(f927,plain,(
% 2.38/0.68    ( ! [X8,X7] : (k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7)) | X7 = X8) )),
% 2.38/0.68    inference(superposition,[],[f511,f80])).
% 2.38/0.68  fof(f80,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.38/0.68    inference(cnf_transformation,[],[f49])).
% 2.38/0.68  fof(f511,plain,(
% 2.38/0.68    ( ! [X10,X9] : (k3_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 2.38/0.68    inference(superposition,[],[f501,f64])).
% 2.38/0.68  fof(f150,plain,(
% 2.38/0.68    ( ! [X6,X7] : (~r1_tarski(X6,k3_xboole_0(X6,X7)) | k3_xboole_0(X6,X7) = X6) )),
% 2.38/0.68    inference(resolution,[],[f69,f112])).
% 2.38/0.68  fof(f96,plain,(
% 2.38/0.68    ( ! [X0,X1] : (sK5(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) )),
% 2.38/0.68    inference(inner_rewriting,[],[f76])).
% 2.38/0.68  fof(f76,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f47])).
% 2.38/0.68  fof(f299,plain,(
% 2.38/0.68    ( ! [X8] : (k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k2_xboole_0(k1_xboole_0,X8))) )),
% 2.38/0.68    inference(superposition,[],[f65,f99])).
% 2.38/0.68  fof(f777,plain,(
% 2.38/0.68    k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))),
% 2.38/0.68    inference(forward_demodulation,[],[f753,f99])).
% 2.38/0.68  fof(f753,plain,(
% 2.38/0.68    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_xboole_0,sK2))),
% 2.38/0.68    inference(backward_demodulation,[],[f514,f729])).
% 2.38/0.68  fof(f514,plain,(
% 2.38/0.68    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.38/0.68    inference(superposition,[],[f501,f307])).
% 2.38/0.68  % SZS output end Proof for theBenchmark
% 2.38/0.68  % (28219)------------------------------
% 2.38/0.68  % (28219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.68  % (28219)Termination reason: Refutation
% 2.38/0.68  
% 2.38/0.68  % (28219)Memory used [KB]: 7419
% 2.38/0.68  % (28219)Time elapsed: 0.245 s
% 2.38/0.68  % (28219)------------------------------
% 2.38/0.68  % (28219)------------------------------
% 2.38/0.68  % (28210)Success in time 0.311 s
%------------------------------------------------------------------------------
