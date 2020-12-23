%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:30 EST 2020

% Result     : Theorem 29.66s
% Output     : Refutation 30.20s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 909 expanded)
%              Number of leaves         :   21 ( 226 expanded)
%              Depth                    :   34
%              Number of atoms          :  486 (4084 expanded)
%              Number of equality atoms :  213 (1281 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59888,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f53109,f58791,f59879])).

fof(f59879,plain,(
    r1_tarski(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f59704])).

fof(f59704,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f77,f59672])).

fof(f59672,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f59663,f56])).

fof(f56,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f59663,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f59618])).

fof(f59618,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f74,f59451])).

fof(f59451,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f59131,f451])).

fof(f451,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f423,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f423,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(resolution,[],[f412,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f412,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f162,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f162,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(k4_xboole_0(X4,X5),X6),X4)
      | r1_tarski(k4_xboole_0(X4,X5),X6) ) ),
    inference(resolution,[],[f100,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f59131,plain,(
    ! [X7] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X7,sK3))) ),
    inference(superposition,[],[f36051,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f36051,plain,(
    ! [X61,X62] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X61,k4_xboole_0(X62,sK3))) ),
    inference(superposition,[],[f19669,f55])).

fof(f55,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f19669,plain,(
    ! [X30,X31,X29,X32] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X32,k4_xboole_0(X30,X29))) ),
    inference(forward_demodulation,[],[f19510,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f19510,plain,(
    ! [X30,X31,X29,X32] : k2_zfmisc_1(k3_xboole_0(X31,X32),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X32,k4_xboole_0(X30,X29))) ),
    inference(superposition,[],[f93,f287])).

fof(f287,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(resolution,[],[f279,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f279,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f278,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f278,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f203,f193])).

fof(f193,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK6(X3,X4),X4)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f65,f102])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),k4_xboole_0(X2,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f192,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f192,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK6(X1,X2),X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58791,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f58788,f31842])).

fof(f31842,plain,(
    r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f528,f31726])).

fof(f31726,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f31725,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f31725,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f31696,f56])).

fof(f31696,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f31654])).

fof(f31654,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f74,f30588])).

fof(f30588,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f30260,f96])).

fof(f30260,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k1_xboole_0)
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f19758,f27113])).

fof(f27113,plain,(
    ! [X2] :
      ( k1_xboole_0 = k3_xboole_0(X2,sK3)
      | sK2 = k3_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f25101,f64])).

fof(f25101,plain,(
    ! [X4] :
      ( k1_xboole_0 = k3_xboole_0(sK3,X4)
      | sK2 = k3_xboole_0(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f25100,f64])).

fof(f25100,plain,(
    ! [X4] :
      ( k1_xboole_0 = k3_xboole_0(sK3,X4)
      | sK2 = k3_xboole_0(sK2,sK0) ) ),
    inference(resolution,[],[f24871,f67])).

fof(f24871,plain,(
    ! [X59] :
      ( r1_tarski(sK2,sK0)
      | k1_xboole_0 = k3_xboole_0(sK3,X59) ) ),
    inference(trivial_inequality_removal,[],[f24468])).

fof(f24468,plain,(
    ! [X59] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK2,sK0)
      | k1_xboole_0 = k3_xboole_0(sK3,X59) ) ),
    inference(superposition,[],[f77,f22793])).

fof(f22793,plain,(
    ! [X58] :
      ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
      | k1_xboole_0 = k3_xboole_0(sK3,X58) ) ),
    inference(trivial_inequality_removal,[],[f22751])).

fof(f22751,plain,(
    ! [X58] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k4_xboole_0(sK2,sK0)
      | k1_xboole_0 = k3_xboole_0(sK3,X58) ) ),
    inference(superposition,[],[f74,f21312])).

fof(f21312,plain,(
    ! [X11] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X11)) ),
    inference(forward_demodulation,[],[f21259,f121])).

fof(f121,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f106,f64])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f104,f62])).

fof(f104,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f21259,plain,(
    ! [X11] : k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X11)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK2,sK0),X11)) ),
    inference(superposition,[],[f80,f21076])).

fof(f21076,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f20782,f451])).

fof(f20782,plain,(
    ! [X11] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X11,sK0)),sK3) ),
    inference(superposition,[],[f19647,f1666])).

fof(f1666,plain,(
    ! [X4] : k2_zfmisc_1(k3_xboole_0(sK2,X4),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) ),
    inference(superposition,[],[f79,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f19647,plain,(
    ! [X30,X31,X29,X32] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(k4_xboole_0(X30,X29),X32)) ),
    inference(forward_demodulation,[],[f19473,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19473,plain,(
    ! [X30,X31,X29,X32] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X31,X32)) = k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(k4_xboole_0(X30,X29),X32)) ),
    inference(superposition,[],[f93,f287])).

fof(f19758,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f19755,f2588])).

fof(f2588,plain,(
    ! [X90,X88,X89] : r1_tarski(k2_zfmisc_1(X88,k3_xboole_0(X89,X90)),k2_zfmisc_1(X88,X89)) ),
    inference(superposition,[],[f528,f80])).

fof(f19755,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f19742,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f19742,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f19698,f63])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f19698,plain,(
    ! [X136] : r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X136,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f19697,f80])).

fof(f19697,plain,(
    ! [X136] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X136),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f19574,f55])).

fof(f19574,plain,(
    ! [X136] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X136),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f3605,f93])).

fof(f3605,plain,(
    ! [X13] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f2584,f3582])).

fof(f3582,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f3530,f64])).

fof(f3530,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f1666,f80])).

fof(f2584,plain,(
    ! [X78,X76,X77] : r1_tarski(k2_zfmisc_1(X76,k3_xboole_0(X77,X78)),k2_zfmisc_1(X76,X78)) ),
    inference(superposition,[],[f514,f80])).

fof(f514,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f167,f73])).

fof(f167,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(k3_xboole_0(X4,X5),X6),X5)
      | r1_tarski(k3_xboole_0(X4,X5),X6) ) ),
    inference(resolution,[],[f102,f72])).

fof(f528,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f514,f64])).

fof(f58788,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f58686,f70])).

fof(f58686,plain,(
    r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f58511])).

fof(f58511,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f77,f58480])).

fof(f58480,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f58477,f57])).

fof(f58477,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f58432])).

fof(f58432,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f74,f58271])).

fof(f58271,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f57951,f451])).

fof(f57951,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,sK2)),sK1) ),
    inference(superposition,[],[f20753,f79])).

fof(f20753,plain,(
    ! [X39,X38] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X38,sK2),X39)) ),
    inference(superposition,[],[f19647,f55])).

fof(f53109,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f52967,f70])).

fof(f52967,plain,(
    r1_tarski(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f52793])).

fof(f52793,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f77,f52668])).

fof(f52668,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f52667,f57])).

fof(f52667,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f52635,f56])).

fof(f52635,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f52590])).

fof(f52590,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f74,f48781])).

fof(f48781,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f45405,f55])).

fof(f45405,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f20782,f42098])).

fof(f42098,plain,(
    ! [X4] :
      ( k1_xboole_0 = k4_xboole_0(sK3,sK1)
      | sK2 = k3_xboole_0(sK2,X4) ) ),
    inference(resolution,[],[f41867,f67])).

fof(f41867,plain,(
    ! [X36] :
      ( r1_tarski(sK2,X36)
      | k1_xboole_0 = k4_xboole_0(sK3,sK1) ) ),
    inference(trivial_inequality_removal,[],[f41422])).

fof(f41422,plain,(
    ! [X36] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK2,X36)
      | k1_xboole_0 = k4_xboole_0(sK3,sK1) ) ),
    inference(superposition,[],[f77,f38571])).

fof(f38571,plain,(
    ! [X33] :
      ( k1_xboole_0 = k4_xboole_0(sK2,X33)
      | k1_xboole_0 = k4_xboole_0(sK3,sK1) ) ),
    inference(trivial_inequality_removal,[],[f38526])).

fof(f38526,plain,(
    ! [X33] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k4_xboole_0(sK2,X33)
      | k1_xboole_0 = k4_xboole_0(sK3,sK1) ) ),
    inference(superposition,[],[f74,f37708])).

fof(f37708,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,X0),k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f36590,f184])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f70,f146])).

fof(f146,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f143,f106])).

fof(f143,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(resolution,[],[f72,f104])).

fof(f36590,plain,(
    ! [X21] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X21),k4_xboole_0(sK3,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f1729,f36385])).

fof(f36385,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f36086,f451])).

fof(f36086,plain,(
    ! [X15] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X15,sK1))) ),
    inference(superposition,[],[f19669,f2554])).

fof(f2554,plain,(
    ! [X4] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X4)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X4)) ),
    inference(superposition,[],[f80,f55])).

fof(f1729,plain,(
    ! [X41,X42,X40] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X40,X41),X42),k2_zfmisc_1(X40,X42)) ),
    inference(superposition,[],[f1694,f423])).

fof(f1694,plain,(
    ! [X76,X74,X75] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X74,X76),X75),k2_zfmisc_1(X76,X75)) ),
    inference(superposition,[],[f514,f79])).

fof(f58,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (19434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (19426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (19418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (19420)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.54  % (19416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (19415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (19419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.55  % (19417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.55  % (19440)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (19439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.56  % (19427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.56  % (19432)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.56  % (19414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.56  % (19431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.56  % (19412)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.56  % (19413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.56  % (19423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (19424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.56  % (19435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.56  % (19422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.57  % (19428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.57  % (19438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.57  % (19433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.57  % (19436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.58  % (19441)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.58  % (19430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.58  % (19425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.58  % (19421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.59  % (19437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.60  % (19429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 3.40/0.82  % (19417)Time limit reached!
% 3.40/0.82  % (19417)------------------------------
% 3.40/0.82  % (19417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.82  % (19417)Termination reason: Time limit
% 3.40/0.82  
% 3.40/0.82  % (19417)Memory used [KB]: 8059
% 3.40/0.82  % (19417)Time elapsed: 0.414 s
% 3.40/0.82  % (19417)------------------------------
% 3.40/0.82  % (19417)------------------------------
% 3.87/0.89  % (19522)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.87/0.92  % (19412)Time limit reached!
% 3.87/0.92  % (19412)------------------------------
% 3.87/0.92  % (19412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.92  % (19412)Termination reason: Time limit
% 3.87/0.92  
% 3.87/0.92  % (19412)Memory used [KB]: 4093
% 3.87/0.92  % (19412)Time elapsed: 0.514 s
% 3.87/0.92  % (19412)------------------------------
% 3.87/0.92  % (19412)------------------------------
% 3.87/0.92  % (19413)Time limit reached!
% 3.87/0.92  % (19413)------------------------------
% 3.87/0.92  % (19413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.92  % (19413)Termination reason: Time limit
% 3.87/0.92  
% 3.87/0.92  % (19413)Memory used [KB]: 8187
% 3.87/0.92  % (19413)Time elapsed: 0.513 s
% 3.87/0.92  % (19413)------------------------------
% 3.87/0.92  % (19413)------------------------------
% 3.87/0.92  % (19424)Time limit reached!
% 3.87/0.92  % (19424)------------------------------
% 3.87/0.92  % (19424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.92  % (19424)Termination reason: Time limit
% 3.87/0.92  
% 3.87/0.92  % (19424)Memory used [KB]: 8443
% 3.87/0.92  % (19424)Time elapsed: 0.518 s
% 3.87/0.92  % (19424)------------------------------
% 3.87/0.92  % (19424)------------------------------
% 3.87/0.93  % (19422)Time limit reached!
% 3.87/0.93  % (19422)------------------------------
% 3.87/0.93  % (19422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.94  % (19422)Termination reason: Time limit
% 3.87/0.94  
% 3.87/0.94  % (19422)Memory used [KB]: 17270
% 3.87/0.94  % (19422)Time elapsed: 0.518 s
% 3.87/0.94  % (19422)------------------------------
% 3.87/0.94  % (19422)------------------------------
% 3.87/0.95  % (19429)Time limit reached!
% 3.87/0.95  % (19429)------------------------------
% 3.87/0.95  % (19429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.96  % (19429)Termination reason: Time limit
% 3.87/0.96  
% 3.87/0.96  % (19429)Memory used [KB]: 12792
% 3.87/0.96  % (19429)Time elapsed: 0.519 s
% 3.87/0.96  % (19429)------------------------------
% 3.87/0.96  % (19429)------------------------------
% 4.79/1.02  % (19419)Time limit reached!
% 4.79/1.02  % (19419)------------------------------
% 4.79/1.02  % (19419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.02  % (19440)Time limit reached!
% 4.79/1.02  % (19440)------------------------------
% 4.79/1.02  % (19440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.02  % (19428)Time limit reached!
% 4.79/1.02  % (19428)------------------------------
% 4.79/1.02  % (19428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.02  % (19428)Termination reason: Time limit
% 4.79/1.02  
% 4.79/1.02  % (19428)Memory used [KB]: 17270
% 4.79/1.02  % (19428)Time elapsed: 0.615 s
% 4.79/1.02  % (19428)------------------------------
% 4.79/1.02  % (19428)------------------------------
% 4.79/1.03  % (19419)Termination reason: Time limit
% 4.79/1.03  
% 4.79/1.03  % (19419)Memory used [KB]: 12025
% 4.79/1.03  % (19419)Time elapsed: 0.604 s
% 4.79/1.03  % (19419)------------------------------
% 4.79/1.03  % (19419)------------------------------
% 5.11/1.04  % (19440)Termination reason: Time limit
% 5.11/1.04  % (19440)Termination phase: Saturation
% 5.11/1.04  
% 5.11/1.04  % (19440)Memory used [KB]: 10234
% 5.11/1.04  % (19440)Time elapsed: 0.600 s
% 5.11/1.04  % (19440)------------------------------
% 5.11/1.04  % (19440)------------------------------
% 5.11/1.04  % (19583)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.15/1.05  % (19582)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.15/1.06  % (19584)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.15/1.08  % (19592)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.15/1.09  % (19598)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.85/1.16  % (19618)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.85/1.16  % (19613)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.85/1.16  % (19612)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.30/1.22  % (19433)Time limit reached!
% 6.30/1.22  % (19433)------------------------------
% 6.30/1.22  % (19433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.30/1.22  % (19433)Termination reason: Time limit
% 6.30/1.22  
% 6.30/1.22  % (19433)Memory used [KB]: 6268
% 6.30/1.22  % (19433)Time elapsed: 0.816 s
% 6.30/1.22  % (19433)------------------------------
% 6.30/1.22  % (19433)------------------------------
% 7.56/1.35  % (19679)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.56/1.38  % (19584)Time limit reached!
% 7.56/1.38  % (19584)------------------------------
% 7.56/1.38  % (19584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.56/1.39  % (19592)Time limit reached!
% 7.56/1.39  % (19592)------------------------------
% 7.56/1.39  % (19592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.56/1.39  % (19592)Termination reason: Time limit
% 7.56/1.39  
% 7.56/1.39  % (19592)Memory used [KB]: 13688
% 7.56/1.39  % (19592)Time elapsed: 0.420 s
% 7.56/1.39  % (19592)------------------------------
% 7.56/1.39  % (19592)------------------------------
% 7.56/1.40  % (19584)Termination reason: Time limit
% 7.56/1.40  
% 7.56/1.40  % (19584)Memory used [KB]: 7931
% 7.56/1.40  % (19584)Time elapsed: 0.429 s
% 7.56/1.40  % (19584)------------------------------
% 7.56/1.40  % (19584)------------------------------
% 8.10/1.42  % (19414)Time limit reached!
% 8.10/1.42  % (19414)------------------------------
% 8.10/1.42  % (19414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.10/1.42  % (19414)Termination reason: Time limit
% 8.10/1.42  % (19414)Termination phase: Saturation
% 8.10/1.42  
% 8.10/1.42  % (19414)Memory used [KB]: 17910
% 8.10/1.42  % (19414)Time elapsed: 1.0000 s
% 8.10/1.42  % (19414)------------------------------
% 8.10/1.42  % (19414)------------------------------
% 8.54/1.51  % (19681)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.54/1.53  % (19680)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.54/1.55  % (19683)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.96/1.64  % (19438)Time limit reached!
% 9.96/1.64  % (19438)------------------------------
% 9.96/1.64  % (19438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.96/1.64  % (19438)Termination reason: Time limit
% 9.96/1.64  
% 9.96/1.64  % (19438)Memory used [KB]: 20084
% 9.96/1.64  % (19438)Time elapsed: 1.212 s
% 9.96/1.64  % (19438)------------------------------
% 9.96/1.64  % (19438)------------------------------
% 10.12/1.67  % (19434)Time limit reached!
% 10.12/1.67  % (19434)------------------------------
% 10.12/1.67  % (19434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.68  % (19434)Termination reason: Time limit
% 10.12/1.68  
% 10.12/1.68  % (19434)Memory used [KB]: 18933
% 10.12/1.68  % (19434)Time elapsed: 1.221 s
% 10.12/1.68  % (19434)------------------------------
% 10.12/1.68  % (19434)------------------------------
% 10.12/1.71  % (19427)Time limit reached!
% 10.12/1.71  % (19427)------------------------------
% 10.12/1.71  % (19427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.72  % (19427)Termination reason: Time limit
% 10.12/1.72  % (19427)Termination phase: Saturation
% 10.12/1.72  
% 10.12/1.72  % (19427)Memory used [KB]: 16758
% 10.12/1.72  % (19427)Time elapsed: 1.300 s
% 10.12/1.72  % (19427)------------------------------
% 10.12/1.72  % (19427)------------------------------
% 10.71/1.74  % (19436)Time limit reached!
% 10.71/1.74  % (19436)------------------------------
% 10.71/1.74  % (19436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.71/1.74  % (19436)Termination reason: Time limit
% 10.71/1.74  
% 10.71/1.74  % (19436)Memory used [KB]: 20980
% 10.71/1.74  % (19436)Time elapsed: 1.316 s
% 10.71/1.74  % (19436)------------------------------
% 10.71/1.74  % (19436)------------------------------
% 11.08/1.78  % (19684)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.08/1.82  % (19685)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.62/1.86  % (19687)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.62/1.87  % (19686)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.77/1.92  % (19439)Time limit reached!
% 11.77/1.92  % (19439)------------------------------
% 11.77/1.92  % (19439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.92  % (19439)Termination reason: Time limit
% 12.15/1.92  
% 12.15/1.92  % (19439)Memory used [KB]: 18166
% 12.15/1.92  % (19439)Time elapsed: 1.511 s
% 12.15/1.92  % (19439)------------------------------
% 12.15/1.92  % (19439)------------------------------
% 12.15/1.94  % (19416)Time limit reached!
% 12.15/1.94  % (19416)------------------------------
% 12.15/1.94  % (19416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.94  % (19416)Termination reason: Time limit
% 12.15/1.94  % (19416)Termination phase: Saturation
% 12.15/1.94  
% 12.15/1.94  % (19416)Memory used [KB]: 23155
% 12.15/1.94  % (19416)Time elapsed: 1.500 s
% 12.15/1.94  % (19416)------------------------------
% 12.15/1.94  % (19416)------------------------------
% 12.27/1.96  % (19683)Time limit reached!
% 12.27/1.96  % (19683)------------------------------
% 12.27/1.96  % (19683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.27/1.96  % (19683)Termination reason: Time limit
% 12.27/1.96  
% 12.27/1.96  % (19683)Memory used [KB]: 3837
% 12.27/1.96  % (19683)Time elapsed: 0.517 s
% 12.27/1.96  % (19683)------------------------------
% 12.27/1.96  % (19683)------------------------------
% 12.77/2.05  % (19688)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.77/2.05  % (19689)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.10/2.09  % (19690)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.55/2.18  % (19687)Time limit reached!
% 13.55/2.18  % (19687)------------------------------
% 13.55/2.18  % (19687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.55/2.18  % (19687)Termination reason: Time limit
% 13.55/2.18  
% 13.55/2.18  % (19687)Memory used [KB]: 4349
% 13.55/2.18  % (19687)Time elapsed: 0.406 s
% 13.55/2.18  % (19687)------------------------------
% 13.55/2.18  % (19687)------------------------------
% 14.95/2.28  % (19612)Time limit reached!
% 14.95/2.28  % (19612)------------------------------
% 14.95/2.28  % (19612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.95/2.28  % (19612)Termination reason: Time limit
% 14.95/2.29  % (19426)Time limit reached!
% 14.95/2.29  % (19426)------------------------------
% 14.95/2.29  % (19426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.95/2.29  % (19426)Termination reason: Time limit
% 14.95/2.29  
% 14.95/2.29  % (19426)Memory used [KB]: 5756
% 14.95/2.29  % (19426)Time elapsed: 1.815 s
% 14.95/2.29  % (19426)------------------------------
% 14.95/2.29  % (19426)------------------------------
% 14.95/2.29  
% 14.95/2.29  % (19612)Memory used [KB]: 14711
% 14.95/2.29  % (19612)Time elapsed: 1.235 s
% 14.95/2.29  % (19612)------------------------------
% 14.95/2.29  % (19612)------------------------------
% 15.49/2.33  % (19691)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 15.77/2.40  % (19693)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.77/2.42  % (19692)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.77/2.43  % (19690)Time limit reached!
% 15.77/2.43  % (19690)------------------------------
% 15.77/2.43  % (19690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.77/2.43  % (19690)Termination reason: Time limit
% 15.77/2.43  
% 15.77/2.43  % (19690)Memory used [KB]: 3070
% 15.77/2.43  % (19690)Time elapsed: 0.434 s
% 15.77/2.43  % (19690)------------------------------
% 15.77/2.43  % (19690)------------------------------
% 16.34/2.45  % (19418)Time limit reached!
% 16.34/2.45  % (19418)------------------------------
% 16.34/2.45  % (19418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.34/2.46  % (19430)Time limit reached!
% 16.34/2.46  % (19430)------------------------------
% 16.34/2.46  % (19430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.34/2.46  % (19430)Termination reason: Time limit
% 16.34/2.46  
% 16.34/2.46  % (19430)Memory used [KB]: 17014
% 16.34/2.46  % (19430)Time elapsed: 2.032 s
% 16.34/2.46  % (19430)------------------------------
% 16.34/2.46  % (19430)------------------------------
% 16.34/2.46  % (19418)Termination reason: Time limit
% 16.34/2.46  
% 16.34/2.46  % (19418)Memory used [KB]: 23155
% 16.34/2.46  % (19418)Time elapsed: 2.005 s
% 16.34/2.46  % (19418)------------------------------
% 16.34/2.46  % (19418)------------------------------
% 16.60/2.53  % (19423)Time limit reached!
% 16.60/2.53  % (19423)------------------------------
% 16.60/2.53  % (19423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.94/2.54  % (19423)Termination reason: Time limit
% 16.94/2.54  
% 16.94/2.54  % (19423)Memory used [KB]: 24562
% 16.94/2.54  % (19423)Time elapsed: 2.097 s
% 16.94/2.54  % (19423)------------------------------
% 16.94/2.54  % (19423)------------------------------
% 17.11/2.57  % (19694)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.11/2.57  % (19695)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.11/2.60  % (19696)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.50/2.66  % (19583)Time limit reached!
% 17.50/2.66  % (19583)------------------------------
% 17.50/2.66  % (19583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.67  % (19583)Termination reason: Time limit
% 17.79/2.67  
% 17.79/2.67  % (19583)Memory used [KB]: 22259
% 17.79/2.67  % (19583)Time elapsed: 1.708 s
% 17.79/2.67  % (19583)------------------------------
% 17.79/2.67  % (19583)------------------------------
% 17.79/2.67  % (19697)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.90/2.77  % (19698)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.76/2.88  % (19618)Time limit reached!
% 19.76/2.88  % (19618)------------------------------
% 19.76/2.88  % (19618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.76/2.88  % (19618)Termination reason: Time limit
% 19.76/2.88  
% 19.76/2.88  % (19618)Memory used [KB]: 20980
% 19.76/2.88  % (19618)Time elapsed: 1.729 s
% 19.76/2.88  % (19618)------------------------------
% 19.76/2.88  % (19618)------------------------------
% 20.18/2.94  % (19695)Time limit reached!
% 20.18/2.94  % (19695)------------------------------
% 20.18/2.94  % (19695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.18/2.94  % (19695)Termination reason: Time limit
% 20.18/2.94  
% 20.18/2.94  % (19695)Memory used [KB]: 10362
% 20.18/2.94  % (19695)Time elapsed: 0.412 s
% 20.18/2.94  % (19695)------------------------------
% 20.18/2.94  % (19695)------------------------------
% 20.56/2.96  % (19686)Time limit reached!
% 20.56/2.96  % (19686)------------------------------
% 20.56/2.96  % (19686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/2.96  % (19686)Termination reason: Time limit
% 20.56/2.96  % (19686)Termination phase: Saturation
% 20.56/2.96  
% 20.56/2.96  % (19686)Memory used [KB]: 17782
% 20.56/2.96  % (19686)Time elapsed: 1.212 s
% 20.56/2.96  % (19686)------------------------------
% 20.56/2.96  % (19686)------------------------------
% 20.56/2.97  % (19697)Time limit reached!
% 20.56/2.97  % (19697)------------------------------
% 20.56/2.97  % (19697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/2.97  % (19697)Termination reason: Time limit
% 20.56/2.97  
% 20.56/2.97  % (19697)Memory used [KB]: 12281
% 20.56/2.97  % (19697)Time elapsed: 0.404 s
% 20.56/2.97  % (19697)------------------------------
% 20.56/2.97  % (19697)------------------------------
% 20.56/3.01  % (19431)Time limit reached!
% 20.56/3.01  % (19431)------------------------------
% 20.56/3.01  % (19431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/3.01  % (19431)Termination reason: Time limit
% 20.56/3.01  % (19431)Termination phase: Saturation
% 20.56/3.01  
% 20.56/3.01  % (19431)Memory used [KB]: 31598
% 20.56/3.01  % (19431)Time elapsed: 2.600 s
% 20.56/3.01  % (19431)------------------------------
% 20.56/3.01  % (19431)------------------------------
% 22.99/3.34  % (19689)Time limit reached!
% 22.99/3.34  % (19689)------------------------------
% 22.99/3.34  % (19689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.99/3.34  % (19689)Termination reason: Time limit
% 22.99/3.34  % (19689)Termination phase: Saturation
% 22.99/3.34  
% 22.99/3.34  % (19689)Memory used [KB]: 10490
% 22.99/3.34  % (19689)Time elapsed: 1.300 s
% 22.99/3.34  % (19689)------------------------------
% 22.99/3.34  % (19689)------------------------------
% 24.04/3.44  % (19425)Time limit reached!
% 24.04/3.44  % (19425)------------------------------
% 24.04/3.44  % (19425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.04/3.44  % (19425)Termination reason: Time limit
% 24.04/3.44  
% 24.04/3.44  % (19425)Memory used [KB]: 18293
% 24.04/3.44  % (19425)Time elapsed: 3.030 s
% 24.04/3.44  % (19425)------------------------------
% 24.04/3.44  % (19425)------------------------------
% 25.38/3.52  % (19420)Time limit reached!
% 25.38/3.52  % (19420)------------------------------
% 25.38/3.52  % (19420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.38/3.53  % (19420)Termination reason: Time limit
% 25.38/3.53  % (19420)Termination phase: Saturation
% 25.38/3.53  
% 25.38/3.53  % (19420)Memory used [KB]: 32494
% 25.38/3.53  % (19420)Time elapsed: 2.500 s
% 25.38/3.53  % (19420)------------------------------
% 25.38/3.53  % (19420)------------------------------
% 27.30/3.80  % (19582)Time limit reached!
% 27.30/3.80  % (19582)------------------------------
% 27.30/3.80  % (19582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.30/3.80  % (19582)Termination reason: Time limit
% 27.30/3.80  
% 27.30/3.80  % (19582)Memory used [KB]: 25841
% 27.30/3.80  % (19582)Time elapsed: 2.835 s
% 27.30/3.80  % (19582)------------------------------
% 27.30/3.80  % (19582)------------------------------
% 29.66/4.10  % (19679)Refutation found. Thanks to Tanya!
% 29.66/4.10  % SZS status Theorem for theBenchmark
% 29.66/4.10  % SZS output start Proof for theBenchmark
% 30.20/4.11  fof(f59888,plain,(
% 30.20/4.11    $false),
% 30.20/4.11    inference(global_subsumption,[],[f58,f53109,f58791,f59879])).
% 30.20/4.11  fof(f59879,plain,(
% 30.20/4.11    r1_tarski(sK1,sK3)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f59704])).
% 30.20/4.11  fof(f59704,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3)),
% 30.20/4.11    inference(superposition,[],[f77,f59672])).
% 30.20/4.11  fof(f59672,plain,(
% 30.20/4.11    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 30.20/4.11    inference(subsumption_resolution,[],[f59663,f56])).
% 30.20/4.11  fof(f56,plain,(
% 30.20/4.11    k1_xboole_0 != sK0),
% 30.20/4.11    inference(cnf_transformation,[],[f27])).
% 30.20/4.11  fof(f27,plain,(
% 30.20/4.11    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).
% 30.20/4.11  fof(f26,plain,(
% 30.20/4.11    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f21,plain,(
% 30.20/4.11    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 30.20/4.11    inference(flattening,[],[f20])).
% 30.20/4.11  fof(f20,plain,(
% 30.20/4.11    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 30.20/4.11    inference(ennf_transformation,[],[f17])).
% 30.20/4.11  fof(f17,negated_conjecture,(
% 30.20/4.11    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 30.20/4.11    inference(negated_conjecture,[],[f16])).
% 30.20/4.11  fof(f16,conjecture,(
% 30.20/4.11    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 30.20/4.11  fof(f59663,plain,(
% 30.20/4.11    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f59618])).
% 30.20/4.11  fof(f59618,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 30.20/4.11    inference(superposition,[],[f74,f59451])).
% 30.20/4.11  fof(f59451,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 30.20/4.11    inference(superposition,[],[f59131,f451])).
% 30.20/4.11  fof(f451,plain,(
% 30.20/4.11    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 30.20/4.11    inference(superposition,[],[f423,f64])).
% 30.20/4.11  fof(f64,plain,(
% 30.20/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f1])).
% 30.20/4.11  fof(f1,axiom,(
% 30.20/4.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 30.20/4.11  fof(f423,plain,(
% 30.20/4.11    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 30.20/4.11    inference(resolution,[],[f412,f67])).
% 30.20/4.11  fof(f67,plain,(
% 30.20/4.11    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 30.20/4.11    inference(cnf_transformation,[],[f24])).
% 30.20/4.11  fof(f24,plain,(
% 30.20/4.11    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 30.20/4.11    inference(ennf_transformation,[],[f11])).
% 30.20/4.11  fof(f11,axiom,(
% 30.20/4.11    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 30.20/4.11  fof(f412,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 30.20/4.11    inference(duplicate_literal_removal,[],[f400])).
% 30.20/4.11  fof(f400,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 30.20/4.11    inference(resolution,[],[f162,f73])).
% 30.20/4.11  fof(f73,plain,(
% 30.20/4.11    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f41])).
% 30.20/4.11  fof(f41,plain,(
% 30.20/4.11    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 30.20/4.11  fof(f40,plain,(
% 30.20/4.11    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f39,plain,(
% 30.20/4.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 30.20/4.11    inference(rectify,[],[f38])).
% 30.20/4.11  fof(f38,plain,(
% 30.20/4.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 30.20/4.11    inference(nnf_transformation,[],[f25])).
% 30.20/4.11  fof(f25,plain,(
% 30.20/4.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 30.20/4.11    inference(ennf_transformation,[],[f3])).
% 30.20/4.11  fof(f3,axiom,(
% 30.20/4.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 30.20/4.11  fof(f162,plain,(
% 30.20/4.11    ( ! [X6,X4,X5] : (r2_hidden(sK7(k4_xboole_0(X4,X5),X6),X4) | r1_tarski(k4_xboole_0(X4,X5),X6)) )),
% 30.20/4.11    inference(resolution,[],[f100,f72])).
% 30.20/4.11  fof(f72,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f41])).
% 30.20/4.11  fof(f100,plain,(
% 30.20/4.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 30.20/4.11    inference(equality_resolution,[],[f81])).
% 30.20/4.11  fof(f81,plain,(
% 30.20/4.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 30.20/4.11    inference(cnf_transformation,[],[f49])).
% 30.20/4.11  fof(f49,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).
% 30.20/4.11  fof(f48,plain,(
% 30.20/4.11    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f47,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(rectify,[],[f46])).
% 30.20/4.11  fof(f46,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(flattening,[],[f45])).
% 30.20/4.11  fof(f45,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(nnf_transformation,[],[f5])).
% 30.20/4.11  fof(f5,axiom,(
% 30.20/4.11    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 30.20/4.11  fof(f59131,plain,(
% 30.20/4.11    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X7,sK3)))) )),
% 30.20/4.11    inference(superposition,[],[f36051,f80])).
% 30.20/4.11  fof(f80,plain,(
% 30.20/4.11    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 30.20/4.11    inference(cnf_transformation,[],[f14])).
% 30.20/4.11  fof(f14,axiom,(
% 30.20/4.11    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 30.20/4.11  fof(f36051,plain,(
% 30.20/4.11    ( ! [X61,X62] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X61,k4_xboole_0(X62,sK3)))) )),
% 30.20/4.11    inference(superposition,[],[f19669,f55])).
% 30.20/4.11  fof(f55,plain,(
% 30.20/4.11    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 30.20/4.11    inference(cnf_transformation,[],[f27])).
% 30.20/4.11  fof(f19669,plain,(
% 30.20/4.11    ( ! [X30,X31,X29,X32] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X32,k4_xboole_0(X30,X29)))) )),
% 30.20/4.11    inference(forward_demodulation,[],[f19510,f96])).
% 30.20/4.11  fof(f96,plain,(
% 30.20/4.11    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 30.20/4.11    inference(equality_resolution,[],[f76])).
% 30.20/4.11  fof(f76,plain,(
% 30.20/4.11    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 30.20/4.11    inference(cnf_transformation,[],[f43])).
% 30.20/4.11  fof(f43,plain,(
% 30.20/4.11    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 30.20/4.11    inference(flattening,[],[f42])).
% 30.20/4.11  fof(f42,plain,(
% 30.20/4.11    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 30.20/4.11    inference(nnf_transformation,[],[f13])).
% 30.20/4.11  fof(f13,axiom,(
% 30.20/4.11    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 30.20/4.11  fof(f19510,plain,(
% 30.20/4.11    ( ! [X30,X31,X29,X32] : (k2_zfmisc_1(k3_xboole_0(X31,X32),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X32,k4_xboole_0(X30,X29)))) )),
% 30.20/4.11    inference(superposition,[],[f93,f287])).
% 30.20/4.11  fof(f287,plain,(
% 30.20/4.11    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 30.20/4.11    inference(resolution,[],[f279,f62])).
% 30.20/4.11  fof(f62,plain,(
% 30.20/4.11    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 30.20/4.11    inference(cnf_transformation,[],[f33])).
% 30.20/4.11  fof(f33,plain,(
% 30.20/4.11    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f32])).
% 30.20/4.11  fof(f32,plain,(
% 30.20/4.11    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f22,plain,(
% 30.20/4.11    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 30.20/4.11    inference(ennf_transformation,[],[f8])).
% 30.20/4.11  fof(f8,axiom,(
% 30.20/4.11    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 30.20/4.11  fof(f279,plain,(
% 30.20/4.11    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 30.20/4.11    inference(resolution,[],[f278,f66])).
% 30.20/4.11  fof(f66,plain,(
% 30.20/4.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 30.20/4.11    inference(cnf_transformation,[],[f35])).
% 30.20/4.11  fof(f35,plain,(
% 30.20/4.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f34])).
% 30.20/4.11  fof(f34,plain,(
% 30.20/4.11    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f23,plain,(
% 30.20/4.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 30.20/4.11    inference(ennf_transformation,[],[f19])).
% 30.20/4.11  fof(f19,plain,(
% 30.20/4.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 30.20/4.11    inference(rectify,[],[f7])).
% 30.20/4.11  fof(f7,axiom,(
% 30.20/4.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 30.20/4.11  fof(f278,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 30.20/4.11    inference(duplicate_literal_removal,[],[f275])).
% 30.20/4.11  fof(f275,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 30.20/4.11    inference(resolution,[],[f203,f193])).
% 30.20/4.11  fof(f193,plain,(
% 30.20/4.11    ( ! [X4,X3] : (r2_hidden(sK6(X3,X4),X4) | r1_xboole_0(X3,X4)) )),
% 30.20/4.11    inference(resolution,[],[f65,f102])).
% 30.20/4.11  fof(f102,plain,(
% 30.20/4.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 30.20/4.11    inference(equality_resolution,[],[f88])).
% 30.20/4.11  fof(f88,plain,(
% 30.20/4.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 30.20/4.11    inference(cnf_transformation,[],[f54])).
% 30.20/4.11  fof(f54,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f53])).
% 30.20/4.11  fof(f53,plain,(
% 30.20/4.11    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 30.20/4.11    introduced(choice_axiom,[])).
% 30.20/4.11  fof(f52,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(rectify,[],[f51])).
% 30.20/4.11  fof(f51,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(flattening,[],[f50])).
% 30.20/4.11  fof(f50,plain,(
% 30.20/4.11    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 30.20/4.11    inference(nnf_transformation,[],[f4])).
% 30.20/4.11  fof(f4,axiom,(
% 30.20/4.11    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 30.20/4.11  fof(f65,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f35])).
% 30.20/4.11  fof(f203,plain,(
% 30.20/4.11    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1),k4_xboole_0(X2,X0)) | r1_xboole_0(X0,X1)) )),
% 30.20/4.11    inference(resolution,[],[f192,f99])).
% 30.20/4.11  fof(f99,plain,(
% 30.20/4.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 30.20/4.11    inference(equality_resolution,[],[f82])).
% 30.20/4.11  fof(f82,plain,(
% 30.20/4.11    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 30.20/4.11    inference(cnf_transformation,[],[f49])).
% 30.20/4.11  fof(f192,plain,(
% 30.20/4.11    ( ! [X2,X1] : (r2_hidden(sK6(X1,X2),X1) | r1_xboole_0(X1,X2)) )),
% 30.20/4.11    inference(resolution,[],[f65,f103])).
% 30.20/4.11  fof(f103,plain,(
% 30.20/4.11    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 30.20/4.11    inference(equality_resolution,[],[f87])).
% 30.20/4.11  fof(f87,plain,(
% 30.20/4.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 30.20/4.11    inference(cnf_transformation,[],[f54])).
% 30.20/4.11  fof(f93,plain,(
% 30.20/4.11    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 30.20/4.11    inference(cnf_transformation,[],[f15])).
% 30.20/4.11  fof(f15,axiom,(
% 30.20/4.11    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 30.20/4.11  fof(f74,plain,(
% 30.20/4.11    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 30.20/4.11    inference(cnf_transformation,[],[f43])).
% 30.20/4.11  fof(f77,plain,(
% 30.20/4.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f44])).
% 30.20/4.11  fof(f44,plain,(
% 30.20/4.11    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 30.20/4.11    inference(nnf_transformation,[],[f10])).
% 30.20/4.11  fof(f10,axiom,(
% 30.20/4.11    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 30.20/4.11  fof(f58791,plain,(
% 30.20/4.11    sK0 = sK2),
% 30.20/4.11    inference(subsumption_resolution,[],[f58788,f31842])).
% 30.20/4.11  fof(f31842,plain,(
% 30.20/4.11    r1_tarski(sK2,sK0)),
% 30.20/4.11    inference(superposition,[],[f528,f31726])).
% 30.20/4.11  fof(f31726,plain,(
% 30.20/4.11    sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(subsumption_resolution,[],[f31725,f57])).
% 30.20/4.11  fof(f57,plain,(
% 30.20/4.11    k1_xboole_0 != sK1),
% 30.20/4.11    inference(cnf_transformation,[],[f27])).
% 30.20/4.11  fof(f31725,plain,(
% 30.20/4.11    k1_xboole_0 = sK1 | sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(subsumption_resolution,[],[f31696,f56])).
% 30.20/4.11  fof(f31696,plain,(
% 30.20/4.11    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f31654])).
% 30.20/4.11  fof(f31654,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(superposition,[],[f74,f30588])).
% 30.20/4.11  fof(f30588,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(forward_demodulation,[],[f30260,f96])).
% 30.20/4.11  fof(f30260,plain,(
% 30.20/4.11    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k1_xboole_0) | sK2 = k3_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(superposition,[],[f19758,f27113])).
% 30.20/4.11  fof(f27113,plain,(
% 30.20/4.11    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,sK3) | sK2 = k3_xboole_0(sK0,sK2)) )),
% 30.20/4.11    inference(superposition,[],[f25101,f64])).
% 30.20/4.11  fof(f25101,plain,(
% 30.20/4.11    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(sK3,X4) | sK2 = k3_xboole_0(sK0,sK2)) )),
% 30.20/4.11    inference(forward_demodulation,[],[f25100,f64])).
% 30.20/4.11  fof(f25100,plain,(
% 30.20/4.11    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(sK3,X4) | sK2 = k3_xboole_0(sK2,sK0)) )),
% 30.20/4.11    inference(resolution,[],[f24871,f67])).
% 30.20/4.11  fof(f24871,plain,(
% 30.20/4.11    ( ! [X59] : (r1_tarski(sK2,sK0) | k1_xboole_0 = k3_xboole_0(sK3,X59)) )),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f24468])).
% 30.20/4.11  fof(f24468,plain,(
% 30.20/4.11    ( ! [X59] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK2,sK0) | k1_xboole_0 = k3_xboole_0(sK3,X59)) )),
% 30.20/4.11    inference(superposition,[],[f77,f22793])).
% 30.20/4.11  fof(f22793,plain,(
% 30.20/4.11    ( ! [X58] : (k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = k3_xboole_0(sK3,X58)) )),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f22751])).
% 30.20/4.11  fof(f22751,plain,(
% 30.20/4.11    ( ! [X58] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = k3_xboole_0(sK3,X58)) )),
% 30.20/4.11    inference(superposition,[],[f74,f21312])).
% 30.20/4.11  fof(f21312,plain,(
% 30.20/4.11    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X11))) )),
% 30.20/4.11    inference(forward_demodulation,[],[f21259,f121])).
% 30.20/4.11  fof(f121,plain,(
% 30.20/4.11    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 30.20/4.11    inference(superposition,[],[f106,f64])).
% 30.20/4.11  fof(f106,plain,(
% 30.20/4.11    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 30.20/4.11    inference(resolution,[],[f104,f62])).
% 30.20/4.11  fof(f104,plain,(
% 30.20/4.11    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 30.20/4.11    inference(resolution,[],[f66,f59])).
% 30.20/4.11  fof(f59,plain,(
% 30.20/4.11    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 30.20/4.11    inference(cnf_transformation,[],[f12])).
% 30.20/4.11  fof(f12,axiom,(
% 30.20/4.11    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 30.20/4.11  fof(f21259,plain,(
% 30.20/4.11    ( ! [X11] : (k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X11)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK2,sK0),X11))) )),
% 30.20/4.11    inference(superposition,[],[f80,f21076])).
% 30.20/4.11  fof(f21076,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 30.20/4.11    inference(superposition,[],[f20782,f451])).
% 30.20/4.11  fof(f20782,plain,(
% 30.20/4.11    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X11,sK0)),sK3)) )),
% 30.20/4.11    inference(superposition,[],[f19647,f1666])).
% 30.20/4.11  fof(f1666,plain,(
% 30.20/4.11    ( ! [X4] : (k2_zfmisc_1(k3_xboole_0(sK2,X4),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))) )),
% 30.20/4.11    inference(superposition,[],[f79,f55])).
% 30.20/4.11  fof(f79,plain,(
% 30.20/4.11    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 30.20/4.11    inference(cnf_transformation,[],[f14])).
% 30.20/4.11  fof(f19647,plain,(
% 30.20/4.11    ( ! [X30,X31,X29,X32] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(k4_xboole_0(X30,X29),X32))) )),
% 30.20/4.11    inference(forward_demodulation,[],[f19473,f97])).
% 30.20/4.11  fof(f97,plain,(
% 30.20/4.11    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 30.20/4.11    inference(equality_resolution,[],[f75])).
% 30.20/4.11  fof(f75,plain,(
% 30.20/4.11    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 30.20/4.11    inference(cnf_transformation,[],[f43])).
% 30.20/4.11  fof(f19473,plain,(
% 30.20/4.11    ( ! [X30,X31,X29,X32] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X31,X32)) = k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(k4_xboole_0(X30,X29),X32))) )),
% 30.20/4.11    inference(superposition,[],[f93,f287])).
% 30.20/4.11  fof(f19758,plain,(
% 30.20/4.11    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 30.20/4.11    inference(subsumption_resolution,[],[f19755,f2588])).
% 30.20/4.11  fof(f2588,plain,(
% 30.20/4.11    ( ! [X90,X88,X89] : (r1_tarski(k2_zfmisc_1(X88,k3_xboole_0(X89,X90)),k2_zfmisc_1(X88,X89))) )),
% 30.20/4.11    inference(superposition,[],[f528,f80])).
% 30.20/4.11  fof(f19755,plain,(
% 30.20/4.11    ~r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 30.20/4.11    inference(resolution,[],[f19742,f70])).
% 30.20/4.11  fof(f70,plain,(
% 30.20/4.11    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 30.20/4.11    inference(cnf_transformation,[],[f37])).
% 30.20/4.11  fof(f37,plain,(
% 30.20/4.11    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 30.20/4.11    inference(flattening,[],[f36])).
% 30.20/4.11  fof(f36,plain,(
% 30.20/4.11    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 30.20/4.11    inference(nnf_transformation,[],[f9])).
% 30.20/4.11  fof(f9,axiom,(
% 30.20/4.11    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 30.20/4.11  fof(f19742,plain,(
% 30.20/4.11    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 30.20/4.11    inference(superposition,[],[f19698,f63])).
% 30.20/4.11  fof(f63,plain,(
% 30.20/4.11    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 30.20/4.11    inference(cnf_transformation,[],[f18])).
% 30.20/4.11  fof(f18,plain,(
% 30.20/4.11    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 30.20/4.11    inference(rectify,[],[f6])).
% 30.20/4.11  fof(f6,axiom,(
% 30.20/4.11    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 30.20/4.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 30.20/4.11  fof(f19698,plain,(
% 30.20/4.11    ( ! [X136] : (r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X136,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 30.20/4.11    inference(forward_demodulation,[],[f19697,f80])).
% 30.20/4.11  fof(f19697,plain,(
% 30.20/4.11    ( ! [X136] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X136),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 30.20/4.11    inference(forward_demodulation,[],[f19574,f55])).
% 30.20/4.11  fof(f19574,plain,(
% 30.20/4.11    ( ! [X136] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X136),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 30.20/4.11    inference(superposition,[],[f3605,f93])).
% 30.20/4.11  fof(f3605,plain,(
% 30.20/4.11    ( ! [X13] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 30.20/4.11    inference(superposition,[],[f2584,f3582])).
% 30.20/4.11  fof(f3582,plain,(
% 30.20/4.11    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 30.20/4.11    inference(forward_demodulation,[],[f3530,f64])).
% 30.20/4.11  fof(f3530,plain,(
% 30.20/4.11    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 30.20/4.11    inference(superposition,[],[f1666,f80])).
% 30.20/4.11  fof(f2584,plain,(
% 30.20/4.11    ( ! [X78,X76,X77] : (r1_tarski(k2_zfmisc_1(X76,k3_xboole_0(X77,X78)),k2_zfmisc_1(X76,X78))) )),
% 30.20/4.11    inference(superposition,[],[f514,f80])).
% 30.20/4.11  fof(f514,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 30.20/4.11    inference(duplicate_literal_removal,[],[f496])).
% 30.20/4.11  fof(f496,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 30.20/4.11    inference(resolution,[],[f167,f73])).
% 30.20/4.11  fof(f167,plain,(
% 30.20/4.11    ( ! [X6,X4,X5] : (r2_hidden(sK7(k3_xboole_0(X4,X5),X6),X5) | r1_tarski(k3_xboole_0(X4,X5),X6)) )),
% 30.20/4.11    inference(resolution,[],[f102,f72])).
% 30.20/4.11  fof(f528,plain,(
% 30.20/4.11    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X2)) )),
% 30.20/4.11    inference(superposition,[],[f514,f64])).
% 30.20/4.11  fof(f58788,plain,(
% 30.20/4.11    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 30.20/4.11    inference(resolution,[],[f58686,f70])).
% 30.20/4.11  fof(f58686,plain,(
% 30.20/4.11    r1_tarski(sK0,sK2)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f58511])).
% 30.20/4.11  fof(f58511,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2)),
% 30.20/4.11    inference(superposition,[],[f77,f58480])).
% 30.20/4.11  fof(f58480,plain,(
% 30.20/4.11    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 30.20/4.11    inference(subsumption_resolution,[],[f58477,f57])).
% 30.20/4.11  fof(f58477,plain,(
% 30.20/4.11    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f58432])).
% 30.20/4.11  fof(f58432,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 30.20/4.11    inference(superposition,[],[f74,f58271])).
% 30.20/4.11  fof(f58271,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 30.20/4.11    inference(superposition,[],[f57951,f451])).
% 30.20/4.11  fof(f57951,plain,(
% 30.20/4.11    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,sK2)),sK1)) )),
% 30.20/4.11    inference(superposition,[],[f20753,f79])).
% 30.20/4.11  fof(f20753,plain,(
% 30.20/4.11    ( ! [X39,X38] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X38,sK2),X39))) )),
% 30.20/4.11    inference(superposition,[],[f19647,f55])).
% 30.20/4.11  fof(f53109,plain,(
% 30.20/4.11    ~r1_tarski(sK1,sK3) | sK1 = sK3),
% 30.20/4.11    inference(resolution,[],[f52967,f70])).
% 30.20/4.11  fof(f52967,plain,(
% 30.20/4.11    r1_tarski(sK3,sK1)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f52793])).
% 30.20/4.11  fof(f52793,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK1)),
% 30.20/4.11    inference(superposition,[],[f77,f52668])).
% 30.20/4.11  fof(f52668,plain,(
% 30.20/4.11    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(subsumption_resolution,[],[f52667,f57])).
% 30.20/4.11  fof(f52667,plain,(
% 30.20/4.11    k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(subsumption_resolution,[],[f52635,f56])).
% 30.20/4.11  fof(f52635,plain,(
% 30.20/4.11    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f52590])).
% 30.20/4.11  fof(f52590,plain,(
% 30.20/4.11    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(superposition,[],[f74,f48781])).
% 30.20/4.11  fof(f48781,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(superposition,[],[f45405,f55])).
% 30.20/4.11  fof(f45405,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 30.20/4.11    inference(superposition,[],[f20782,f42098])).
% 30.20/4.11  fof(f42098,plain,(
% 30.20/4.11    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(sK3,sK1) | sK2 = k3_xboole_0(sK2,X4)) )),
% 30.20/4.11    inference(resolution,[],[f41867,f67])).
% 30.20/4.11  fof(f41867,plain,(
% 30.20/4.11    ( ! [X36] : (r1_tarski(sK2,X36) | k1_xboole_0 = k4_xboole_0(sK3,sK1)) )),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f41422])).
% 30.20/4.11  fof(f41422,plain,(
% 30.20/4.11    ( ! [X36] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK2,X36) | k1_xboole_0 = k4_xboole_0(sK3,sK1)) )),
% 30.20/4.11    inference(superposition,[],[f77,f38571])).
% 30.20/4.11  fof(f38571,plain,(
% 30.20/4.11    ( ! [X33] : (k1_xboole_0 = k4_xboole_0(sK2,X33) | k1_xboole_0 = k4_xboole_0(sK3,sK1)) )),
% 30.20/4.11    inference(trivial_inequality_removal,[],[f38526])).
% 30.20/4.11  fof(f38526,plain,(
% 30.20/4.11    ( ! [X33] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,X33) | k1_xboole_0 = k4_xboole_0(sK3,sK1)) )),
% 30.20/4.11    inference(superposition,[],[f74,f37708])).
% 30.20/4.11  fof(f37708,plain,(
% 30.20/4.11    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,X0),k4_xboole_0(sK3,sK1))) )),
% 30.20/4.11    inference(resolution,[],[f36590,f184])).
% 30.20/4.11  fof(f184,plain,(
% 30.20/4.11    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 30.20/4.11    inference(resolution,[],[f70,f146])).
% 30.20/4.11  fof(f146,plain,(
% 30.20/4.11    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 30.20/4.11    inference(forward_demodulation,[],[f143,f106])).
% 30.20/4.11  fof(f143,plain,(
% 30.20/4.11    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 30.20/4.11    inference(resolution,[],[f72,f104])).
% 30.20/4.11  fof(f36590,plain,(
% 30.20/4.11    ( ! [X21] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X21),k4_xboole_0(sK3,sK1)),k1_xboole_0)) )),
% 30.20/4.11    inference(superposition,[],[f1729,f36385])).
% 30.20/4.11  fof(f36385,plain,(
% 30.20/4.11    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 30.20/4.11    inference(superposition,[],[f36086,f451])).
% 30.20/4.11  fof(f36086,plain,(
% 30.20/4.11    ( ! [X15] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X15,sK1)))) )),
% 30.20/4.11    inference(superposition,[],[f19669,f2554])).
% 30.20/4.11  fof(f2554,plain,(
% 30.20/4.11    ( ! [X4] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X4)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X4))) )),
% 30.20/4.11    inference(superposition,[],[f80,f55])).
% 30.20/4.11  fof(f1729,plain,(
% 30.20/4.11    ( ! [X41,X42,X40] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X40,X41),X42),k2_zfmisc_1(X40,X42))) )),
% 30.20/4.11    inference(superposition,[],[f1694,f423])).
% 30.20/4.11  fof(f1694,plain,(
% 30.20/4.11    ( ! [X76,X74,X75] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X74,X76),X75),k2_zfmisc_1(X76,X75))) )),
% 30.20/4.11    inference(superposition,[],[f514,f79])).
% 30.20/4.11  fof(f58,plain,(
% 30.20/4.11    sK1 != sK3 | sK0 != sK2),
% 30.20/4.11    inference(cnf_transformation,[],[f27])).
% 30.20/4.11  % SZS output end Proof for theBenchmark
% 30.20/4.11  % (19679)------------------------------
% 30.20/4.11  % (19679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.20/4.11  % (19679)Termination reason: Refutation
% 30.20/4.11  
% 30.20/4.11  % (19679)Memory used [KB]: 52707
% 30.20/4.11  % (19679)Time elapsed: 2.814 s
% 30.20/4.11  % (19679)------------------------------
% 30.20/4.11  % (19679)------------------------------
% 30.20/4.12  % (19411)Success in time 3.76 s
%------------------------------------------------------------------------------
