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
% DateTime   : Thu Dec  3 12:42:33 EST 2020

% Result     : Theorem 32.77s
% Output     : Refutation 33.46s
% Verified   : 
% Statistics : Number of formulae       :  180 (4601 expanded)
%              Number of leaves         :   16 (1115 expanded)
%              Depth                    :   59
%              Number of atoms          :  510 (21252 expanded)
%              Number of equality atoms :  182 (4374 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112493,plain,(
    $false ),
    inference(global_subsumption,[],[f46144,f81058,f112492])).

fof(f112492,plain,(
    r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f112453,f81058])).

fof(f112453,plain,
    ( r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f112245,f52149])).

fof(f52149,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK0)
    | sK0 = sK2 ),
    inference(trivial_inequality_removal,[],[f51893])).

fof(f51893,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK5(sK2,sK0),sK0)
    | sK0 = sK2 ),
    inference(superposition,[],[f69,f46141])).

fof(f46141,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK5(sK2,sK0)))
    | sK0 = sK2 ),
    inference(resolution,[],[f46140,f236])).

fof(f236,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,X6)
      | k4_xboole_0(X5,k1_tarski(sK5(X6,X5))) = X5
      | X5 = X6 ) ),
    inference(resolution,[],[f139,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | k4_xboole_0(X0,k1_tarski(sK5(X1,X0))) = X0 ) ),
    inference(resolution,[],[f70,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f46140,plain,(
    r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f46129])).

fof(f46129,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f45888,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f45888,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(X1,sK2),sK0)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f45571,f65])).

fof(f45571,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f45313,f118])).

fof(f118,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f115,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f100,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),k4_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f92,f55])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f45313,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f91,f45300])).

fof(f45300,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f45298,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).

fof(f20,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f45298,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f45281])).

fof(f45281,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f66,f45220])).

fof(f45220,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f44264,f264])).

fof(f264,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(resolution,[],[f257,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f257,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f104,f65])).

fof(f104,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(k4_xboole_0(X2,X3),X4),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f93,f64])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f44264,plain,(
    ! [X16] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X16,sK2),sK0),sK1) ),
    inference(superposition,[],[f20503,f20653])).

fof(f20653,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f20557,f49])).

fof(f49,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f20557,plain,(
    ! [X37,X35,X38,X36] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(X36,X38)) ),
    inference(forward_demodulation,[],[f20465,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f20465,plain,(
    ! [X37,X35,X38,X36] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(X36,X38)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X37,X38)) ),
    inference(superposition,[],[f85,f577])).

fof(f577,plain,(
    ! [X23,X22] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X22,X23),X23) ),
    inference(resolution,[],[f557,f126])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f59,f120])).

fof(f120,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f118,f64])).

fof(f557,plain,(
    ! [X12,X13,X11] : r1_tarski(k3_xboole_0(k4_xboole_0(X11,X12),X12),X13) ),
    inference(resolution,[],[f546,f64])).

fof(f546,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k4_xboole_0(X1,X2),X2)) ),
    inference(resolution,[],[f545,f54])).

fof(f545,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))
      | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ) ),
    inference(resolution,[],[f156,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f96,f55])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f107,f92])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f95,f55])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f20503,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f85,f97])).

fof(f97,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f56,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112245,plain,(
    ! [X33] :
      ( r2_hidden(sK5(sK2,X33),sK0)
      | r1_tarski(sK2,X33) ) ),
    inference(resolution,[],[f112211,f64])).

fof(f112211,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(condensation,[],[f112167])).

fof(f112167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f111944,f91])).

fof(f111944,plain,(
    ! [X218,X219] :
      ( ~ r2_hidden(X219,k4_xboole_0(X218,sK0))
      | ~ r2_hidden(X219,sK2) ) ),
    inference(subsumption_resolution,[],[f111819,f118])).

fof(f111819,plain,(
    ! [X218,X219] :
      ( r2_hidden(X219,k1_xboole_0)
      | ~ r2_hidden(X219,k4_xboole_0(X218,sK0))
      | ~ r2_hidden(X219,sK2) ) ),
    inference(superposition,[],[f94,f111694])).

fof(f111694,plain,(
    ! [X29] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X29,sK0)) ),
    inference(subsumption_resolution,[],[f111671,f90])).

fof(f111671,plain,(
    ! [X29] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X29,sK0)) ) ),
    inference(superposition,[],[f93716,f672])).

fof(f672,plain,(
    ! [X23,X22] : k1_xboole_0 = k3_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(resolution,[],[f655,f126])).

fof(f655,plain,(
    ! [X12,X13,X11] : r1_tarski(k3_xboole_0(X11,k4_xboole_0(X12,X11)),X13) ),
    inference(resolution,[],[f647,f64])).

fof(f647,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f646,f54])).

fof(f646,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))
      | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ) ),
    inference(resolution,[],[f195,f107])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f111,f92])).

fof(f93716,plain,(
    ! [X38] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X38),sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,X38) ) ),
    inference(subsumption_resolution,[],[f93670,f51])).

fof(f93670,plain,(
    ! [X38] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X38),sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,X38)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f66,f81151])).

fof(f81151,plain,(
    ! [X27] : k2_zfmisc_1(k3_xboole_0(sK2,X27),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X27),sK1) ),
    inference(forward_demodulation,[],[f81128,f20503])).

fof(f81128,plain,(
    ! [X27] : k2_zfmisc_1(k3_xboole_0(sK2,X27),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X27,sK1)) ),
    inference(superposition,[],[f20503,f80739])).

fof(f80739,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(superposition,[],[f49,f80726])).

fof(f80726,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f80687,f22964])).

fof(f22964,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f22960,f59])).

fof(f22960,plain,(
    r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f22949])).

fof(f22949,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f22721,f64])).

fof(f22721,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(X1,sK3),sK1)
      | r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f22407,f65])).

fof(f22407,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f22151,f118])).

fof(f22151,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f91,f22140])).

fof(f22140,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f22139,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f22139,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f22127])).

fof(f22127,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f66,f22093])).

fof(f22093,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f21377,f264])).

fof(f21377,plain,(
    ! [X10] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X10,sK3),sK1)) ),
    inference(superposition,[],[f20457,f20811])).

fof(f20811,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f20603,f49])).

fof(f20603,plain,(
    ! [X37,X35,X38,X36] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X38,X36)) ),
    inference(forward_demodulation,[],[f20511,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20511,plain,(
    ! [X37,X35,X38,X36] : k3_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X38,X36)) = k2_zfmisc_1(k3_xboole_0(X37,X38),k1_xboole_0) ),
    inference(superposition,[],[f85,f577])).

fof(f20457,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f85,f97])).

fof(f80687,plain,
    ( r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f80516,f26613])).

fof(f26613,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK1)
    | sK1 = sK3 ),
    inference(trivial_inequality_removal,[],[f26360])).

fof(f26360,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK5(sK3,sK1),sK1)
    | sK1 = sK3 ),
    inference(superposition,[],[f69,f22961])).

fof(f22961,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK5(sK3,sK1)))
    | sK1 = sK3 ),
    inference(resolution,[],[f22960,f236])).

fof(f80516,plain,(
    ! [X32] :
      ( r2_hidden(sK5(sK3,X32),sK1)
      | r1_tarski(sK3,X32) ) ),
    inference(resolution,[],[f80483,f64])).

fof(f80483,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1) ) ),
    inference(condensation,[],[f80444])).

fof(f80444,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f80419,f91])).

fof(f80419,plain,(
    ! [X206,X207] :
      ( ~ r2_hidden(X207,k4_xboole_0(X206,sK1))
      | ~ r2_hidden(X207,sK3) ) ),
    inference(subsumption_resolution,[],[f80293,f118])).

fof(f80293,plain,(
    ! [X206,X207] :
      ( r2_hidden(X207,k1_xboole_0)
      | ~ r2_hidden(X207,k4_xboole_0(X206,sK1))
      | ~ r2_hidden(X207,sK3) ) ),
    inference(superposition,[],[f94,f80173])).

fof(f80173,plain,(
    ! [X29] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X29,sK1)) ),
    inference(subsumption_resolution,[],[f80150,f89])).

fof(f80150,plain,(
    ! [X29] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X29,sK1)) ) ),
    inference(superposition,[],[f58910,f672])).

fof(f58910,plain,(
    ! [X22] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X22))
      | k1_xboole_0 = k3_xboole_0(sK3,X22) ) ),
    inference(subsumption_resolution,[],[f58877,f50])).

fof(f58877,plain,(
    ! [X22] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X22))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k3_xboole_0(sK3,X22) ) ),
    inference(superposition,[],[f66,f46370])).

fof(f46370,plain,(
    ! [X5] : k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5)) ),
    inference(forward_demodulation,[],[f46352,f20457])).

fof(f46352,plain,(
    ! [X5] : k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X5)) ),
    inference(superposition,[],[f20457,f46319])).

fof(f46319,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(subsumption_resolution,[],[f46317,f23077])).

fof(f23077,plain,(
    ! [X43] : r1_tarski(k2_zfmisc_1(X43,sK1),k2_zfmisc_1(X43,sK3)) ),
    inference(superposition,[],[f21404,f22965])).

fof(f22965,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f22960,f56])).

fof(f21404,plain,(
    ! [X92,X93,X91] : r1_tarski(k2_zfmisc_1(X91,k3_xboole_0(X92,X93)),k2_zfmisc_1(X91,X93)) ),
    inference(superposition,[],[f310,f20457])).

fof(f310,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f108,f65])).

fof(f108,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(k3_xboole_0(X2,X3),X4),X3)
      | r1_tarski(k3_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f95,f64])).

fof(f46317,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(resolution,[],[f46207,f59])).

fof(f46207,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f44465,f46145])).

fof(f46145,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f46140,f56])).

fof(f44465,plain,(
    ! [X14] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X14,sK2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f44296,f49])).

fof(f44296,plain,(
    ! [X99,X97,X98] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X97,X99),X98),k2_zfmisc_1(X99,X98)) ),
    inference(superposition,[],[f310,f20503])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f81058,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f80740])).

fof(f80740,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f52,f80726])).

fof(f52,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f46144,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f46140,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (16345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (16347)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (16345)Refutation not found, incomplete strategy% (16345)------------------------------
% 0.22/0.57  % (16345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (16374)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (16345)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (16345)Memory used [KB]: 1663
% 0.22/0.58  % (16345)Time elapsed: 0.133 s
% 0.22/0.58  % (16345)------------------------------
% 0.22/0.58  % (16345)------------------------------
% 0.22/0.58  % (16347)Refutation not found, incomplete strategy% (16347)------------------------------
% 0.22/0.58  % (16347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (16347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (16347)Memory used [KB]: 10746
% 0.22/0.58  % (16347)Time elapsed: 0.131 s
% 0.22/0.58  % (16347)------------------------------
% 0.22/0.58  % (16347)------------------------------
% 0.22/0.58  % (16367)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.59  % (16359)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (16367)Refutation not found, incomplete strategy% (16367)------------------------------
% 0.22/0.59  % (16367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (16367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (16367)Memory used [KB]: 10746
% 0.22/0.59  % (16367)Time elapsed: 0.143 s
% 0.22/0.59  % (16367)------------------------------
% 0.22/0.59  % (16367)------------------------------
% 0.22/0.60  % (16358)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.60  % (16349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.60  % (16350)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.60  % (16348)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.81/0.61  % (16357)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.81/0.62  % (16368)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.81/0.62  % (16368)Refutation not found, incomplete strategy% (16368)------------------------------
% 1.81/0.62  % (16368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (16368)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  
% 1.81/0.62  % (16368)Memory used [KB]: 1791
% 1.81/0.62  % (16368)Time elapsed: 0.129 s
% 1.81/0.62  % (16368)------------------------------
% 1.81/0.62  % (16368)------------------------------
% 1.81/0.62  % (16346)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.99/0.63  % (16360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.99/0.63  % (16351)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.99/0.63  % (16365)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.99/0.63  % (16370)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.99/0.64  % (16365)Refutation not found, incomplete strategy% (16365)------------------------------
% 1.99/0.64  % (16365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.64  % (16365)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.64  
% 1.99/0.64  % (16365)Memory used [KB]: 10746
% 1.99/0.64  % (16365)Time elapsed: 0.195 s
% 1.99/0.64  % (16365)------------------------------
% 1.99/0.64  % (16365)------------------------------
% 1.99/0.64  % (16369)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.99/0.64  % (16373)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.15/0.64  % (16362)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.15/0.64  % (16352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.15/0.64  % (16361)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.15/0.64  % (16371)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.15/0.65  % (16355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.15/0.65  % (16356)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.15/0.65  % (16354)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.15/0.65  % (16363)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.15/0.66  % (16372)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.15/0.66  % (16366)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.15/0.66  % (16366)Refutation not found, incomplete strategy% (16366)------------------------------
% 2.15/0.66  % (16366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.66  % (16366)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.66  
% 2.15/0.66  % (16366)Memory used [KB]: 1663
% 2.15/0.66  % (16366)Time elapsed: 0.174 s
% 2.15/0.66  % (16366)------------------------------
% 2.15/0.66  % (16366)------------------------------
% 2.15/0.66  % (16364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.15/0.67  % (16353)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.15/0.67  % (16353)Refutation not found, incomplete strategy% (16353)------------------------------
% 2.15/0.67  % (16353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (16353)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (16353)Memory used [KB]: 10746
% 2.15/0.67  % (16353)Time elapsed: 0.224 s
% 2.15/0.67  % (16353)------------------------------
% 2.15/0.67  % (16353)------------------------------
% 2.57/0.74  % (16411)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.57/0.74  % (16411)Refutation not found, incomplete strategy% (16411)------------------------------
% 2.57/0.74  % (16411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.74  % (16411)Termination reason: Refutation not found, incomplete strategy
% 2.57/0.74  
% 2.57/0.74  % (16411)Memory used [KB]: 6268
% 2.57/0.74  % (16411)Time elapsed: 0.065 s
% 2.57/0.74  % (16411)------------------------------
% 2.57/0.74  % (16411)------------------------------
% 2.57/0.75  % (16413)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.95/0.79  % (16412)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.95/0.80  % (16414)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.95/0.81  % (16416)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.95/0.82  % (16417)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.95/0.83  % (16418)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.95/0.85  % (16425)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.42/0.85  % (16350)Time limit reached!
% 3.42/0.85  % (16350)------------------------------
% 3.42/0.85  % (16350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.85  % (16350)Termination reason: Time limit
% 3.42/0.85  
% 3.42/0.85  % (16350)Memory used [KB]: 8059
% 3.42/0.85  % (16350)Time elapsed: 0.418 s
% 3.42/0.85  % (16350)------------------------------
% 3.42/0.85  % (16350)------------------------------
% 3.85/0.94  % (16355)Time limit reached!
% 3.85/0.94  % (16355)------------------------------
% 3.85/0.94  % (16355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.94  % (16355)Termination reason: Time limit
% 3.85/0.94  
% 3.85/0.94  % (16355)Memory used [KB]: 15863
% 3.85/0.94  % (16355)Time elapsed: 0.506 s
% 3.85/0.94  % (16355)------------------------------
% 3.85/0.94  % (16355)------------------------------
% 3.95/0.95  % (16346)Time limit reached!
% 3.95/0.95  % (16346)------------------------------
% 3.95/0.95  % (16346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.95  % (16357)Time limit reached!
% 3.95/0.95  % (16357)------------------------------
% 3.95/0.95  % (16357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.96  % (16357)Termination reason: Time limit
% 3.95/0.96  
% 3.95/0.96  % (16357)Memory used [KB]: 8187
% 3.95/0.96  % (16357)Time elapsed: 0.518 s
% 3.95/0.96  % (16357)------------------------------
% 3.95/0.96  % (16357)------------------------------
% 3.95/0.97  % (16346)Termination reason: Time limit
% 3.95/0.97  
% 3.95/0.97  % (16346)Memory used [KB]: 7547
% 3.95/0.97  % (16346)Time elapsed: 0.517 s
% 3.95/0.97  % (16346)------------------------------
% 3.95/0.97  % (16346)------------------------------
% 3.95/0.97  % (16362)Time limit reached!
% 3.95/0.97  % (16362)------------------------------
% 3.95/0.97  % (16362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.98  % (16362)Termination reason: Time limit
% 3.95/0.98  
% 3.95/0.98  % (16362)Memory used [KB]: 14711
% 3.95/0.98  % (16362)Time elapsed: 0.537 s
% 3.95/0.98  % (16362)------------------------------
% 3.95/0.98  % (16362)------------------------------
% 3.95/0.98  % (16469)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.40/1.04  % (16373)Time limit reached!
% 4.40/1.04  % (16373)------------------------------
% 4.40/1.04  % (16373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/1.06  % (16373)Termination reason: Time limit
% 4.40/1.06  
% 4.40/1.06  % (16373)Memory used [KB]: 8827
% 4.40/1.06  % (16373)Time elapsed: 0.610 s
% 4.40/1.06  % (16373)------------------------------
% 4.40/1.06  % (16373)------------------------------
% 4.40/1.06  % (16414)Time limit reached!
% 4.40/1.06  % (16414)------------------------------
% 4.40/1.06  % (16414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/1.06  % (16414)Termination reason: Time limit
% 4.40/1.06  % (16414)Termination phase: Saturation
% 4.40/1.06  
% 4.40/1.06  % (16414)Memory used [KB]: 7675
% 4.40/1.06  % (16414)Time elapsed: 0.400 s
% 4.40/1.06  % (16414)------------------------------
% 4.40/1.06  % (16414)------------------------------
% 4.40/1.07  % (16518)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.40/1.07  % (16533)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.75/1.08  % (16361)Time limit reached!
% 4.75/1.08  % (16361)------------------------------
% 4.75/1.08  % (16361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.08  % (16361)Termination reason: Time limit
% 4.75/1.08  % (16361)Termination phase: Saturation
% 4.75/1.08  
% 4.75/1.08  % (16361)Memory used [KB]: 16502
% 4.75/1.08  % (16361)Time elapsed: 0.600 s
% 4.75/1.08  % (16361)------------------------------
% 4.75/1.08  % (16361)------------------------------
% 4.75/1.09  % (16531)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.75/1.09  % (16533)Refutation not found, incomplete strategy% (16533)------------------------------
% 4.75/1.09  % (16533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.09  % (16533)Termination reason: Refutation not found, incomplete strategy
% 4.75/1.09  
% 4.75/1.09  % (16531)Refutation not found, incomplete strategy% (16531)------------------------------
% 4.75/1.09  % (16531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.09  % (16531)Termination reason: Refutation not found, incomplete strategy
% 4.75/1.09  
% 4.75/1.09  % (16531)Memory used [KB]: 6268
% 4.75/1.09  % (16531)Time elapsed: 0.095 s
% 4.75/1.09  % (16531)------------------------------
% 4.75/1.09  % (16531)------------------------------
% 4.75/1.09  % (16533)Memory used [KB]: 1791
% 4.75/1.09  % (16533)Time elapsed: 0.099 s
% 4.75/1.09  % (16533)------------------------------
% 4.75/1.09  % (16533)------------------------------
% 4.75/1.09  % (16352)Time limit reached!
% 4.75/1.09  % (16352)------------------------------
% 4.75/1.09  % (16352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.09  % (16352)Termination reason: Time limit
% 4.75/1.09  
% 4.75/1.09  % (16352)Memory used [KB]: 11001
% 4.75/1.09  % (16352)Time elapsed: 0.604 s
% 4.75/1.09  % (16352)------------------------------
% 4.75/1.09  % (16352)------------------------------
% 4.75/1.10  % (16416)Time limit reached!
% 4.75/1.10  % (16416)------------------------------
% 4.75/1.10  % (16416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.10  % (16416)Termination reason: Time limit
% 4.75/1.10  % (16416)Termination phase: Saturation
% 4.75/1.10  
% 4.75/1.10  % (16416)Memory used [KB]: 13432
% 4.75/1.10  % (16416)Time elapsed: 0.400 s
% 4.75/1.10  % (16416)------------------------------
% 4.75/1.10  % (16416)------------------------------
% 4.75/1.11  % (16549)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.24/1.18  % (16580)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.24/1.18  % (16579)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.24/1.18  % (16579)Refutation not found, incomplete strategy% (16579)------------------------------
% 6.24/1.18  % (16579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.24/1.18  % (16579)Termination reason: Refutation not found, incomplete strategy
% 6.24/1.18  
% 6.24/1.18  % (16579)Memory used [KB]: 1663
% 6.24/1.18  % (16579)Time elapsed: 0.106 s
% 6.24/1.18  % (16579)------------------------------
% 6.24/1.18  % (16579)------------------------------
% 6.46/1.20  % (16589)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.46/1.21  % (16588)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.46/1.21  % (16587)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.46/1.21  % (16587)Refutation not found, incomplete strategy% (16587)------------------------------
% 6.46/1.21  % (16587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.46/1.21  % (16587)Termination reason: Refutation not found, incomplete strategy
% 6.46/1.21  
% 6.46/1.21  % (16587)Memory used [KB]: 6268
% 6.46/1.21  % (16587)Time elapsed: 0.117 s
% 6.46/1.21  % (16587)------------------------------
% 6.46/1.21  % (16587)------------------------------
% 6.46/1.23  % (16590)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.80/1.24  % (16591)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.87/1.29  % (16617)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.32/1.35  % (16622)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.67/1.51  % (16549)Time limit reached!
% 8.67/1.51  % (16549)------------------------------
% 8.67/1.51  % (16549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.67/1.51  % (16549)Termination reason: Time limit
% 8.67/1.51  
% 8.67/1.51  % (16549)Memory used [KB]: 3454
% 8.67/1.51  % (16549)Time elapsed: 0.513 s
% 8.67/1.51  % (16549)------------------------------
% 8.67/1.51  % (16549)------------------------------
% 8.67/1.52  % (16588)Time limit reached!
% 8.67/1.52  % (16588)------------------------------
% 8.67/1.52  % (16588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.67/1.52  % (16588)Termination reason: Time limit
% 8.67/1.52  % (16588)Termination phase: Saturation
% 8.67/1.52  
% 8.67/1.52  % (16588)Memory used [KB]: 4477
% 8.67/1.52  % (16588)Time elapsed: 0.400 s
% 8.67/1.52  % (16588)------------------------------
% 8.67/1.52  % (16588)------------------------------
% 9.03/1.54  % (16591)Time limit reached!
% 9.03/1.54  % (16591)------------------------------
% 9.03/1.54  % (16591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.03/1.54  % (16591)Termination reason: Time limit
% 9.03/1.54  % (16591)Termination phase: Saturation
% 9.03/1.54  
% 9.03/1.54  % (16591)Memory used [KB]: 2686
% 9.03/1.54  % (16591)Time elapsed: 0.411 s
% 9.03/1.54  % (16591)------------------------------
% 9.03/1.54  % (16591)------------------------------
% 9.51/1.64  % (16667)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.51/1.64  % (16669)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.25/1.67  % (16668)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.25/1.68  % (16371)Time limit reached!
% 10.25/1.68  % (16371)------------------------------
% 10.25/1.68  % (16371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.68  % (16371)Termination reason: Time limit
% 10.25/1.68  % (16371)Termination phase: Saturation
% 10.25/1.68  
% 10.25/1.68  % (16371)Memory used [KB]: 22259
% 10.25/1.68  % (16371)Time elapsed: 1.200 s
% 10.25/1.68  % (16371)------------------------------
% 10.25/1.68  % (16371)------------------------------
% 11.29/1.81  % (16360)Time limit reached!
% 11.29/1.81  % (16360)------------------------------
% 11.29/1.81  % (16360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.29/1.81  % (16360)Termination reason: Time limit
% 11.29/1.81  % (16360)Termination phase: Saturation
% 11.29/1.81  
% 11.29/1.81  % (16360)Memory used [KB]: 18421
% 11.29/1.81  % (16360)Time elapsed: 1.300 s
% 11.29/1.81  % (16360)------------------------------
% 11.29/1.81  % (16360)------------------------------
% 11.29/1.82  % (16670)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.29/1.82  % (16670)Refutation not found, incomplete strategy% (16670)------------------------------
% 11.29/1.82  % (16670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.29/1.82  % (16670)Termination reason: Refutation not found, incomplete strategy
% 11.29/1.82  
% 11.29/1.82  % (16670)Memory used [KB]: 6268
% 11.29/1.82  % (16670)Time elapsed: 0.089 s
% 11.29/1.82  % (16670)------------------------------
% 11.29/1.82  % (16670)------------------------------
% 11.29/1.82  % (16369)Time limit reached!
% 11.29/1.82  % (16369)------------------------------
% 11.29/1.82  % (16369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.29/1.82  % (16369)Termination reason: Time limit
% 11.29/1.82  
% 11.29/1.82  % (16369)Memory used [KB]: 24818
% 11.29/1.82  % (16369)Time elapsed: 1.346 s
% 11.29/1.82  % (16369)------------------------------
% 11.29/1.82  % (16369)------------------------------
% 11.59/1.92  % (16671)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.31/1.94  % (16418)Time limit reached!
% 12.31/1.94  % (16418)------------------------------
% 12.31/1.94  % (16418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.31/1.94  % (16418)Termination reason: Time limit
% 12.31/1.94  
% 12.31/1.94  % (16418)Memory used [KB]: 14328
% 12.31/1.94  % (16418)Time elapsed: 1.221 s
% 12.31/1.94  % (16418)------------------------------
% 12.31/1.94  % (16418)------------------------------
% 12.31/1.96  % (16372)Time limit reached!
% 12.31/1.96  % (16372)------------------------------
% 12.31/1.96  % (16372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.31/1.96  % (16372)Termination reason: Time limit
% 12.31/1.96  
% 12.31/1.96  % (16372)Memory used [KB]: 16119
% 12.31/1.96  % (16372)Time elapsed: 1.523 s
% 12.31/1.96  % (16372)------------------------------
% 12.31/1.96  % (16372)------------------------------
% 12.31/1.97  % (16672)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.31/1.97  % (16672)Refutation not found, incomplete strategy% (16672)------------------------------
% 12.31/1.97  % (16672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.31/1.98  % (16672)Termination reason: Refutation not found, incomplete strategy
% 12.31/1.98  
% 12.31/1.98  % (16672)Memory used [KB]: 10746
% 12.31/1.98  % (16672)Time elapsed: 0.124 s
% 12.31/1.98  % (16672)------------------------------
% 12.31/1.98  % (16672)------------------------------
% 12.31/1.99  % (16669)Time limit reached!
% 12.31/1.99  % (16669)------------------------------
% 12.31/1.99  % (16669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.31/1.99  % (16669)Termination reason: Time limit
% 12.31/1.99  % (16669)Termination phase: Saturation
% 12.31/1.99  
% 12.31/1.99  % (16669)Memory used [KB]: 11385
% 12.31/1.99  % (16669)Time elapsed: 0.400 s
% 12.31/1.99  % (16669)------------------------------
% 12.31/1.99  % (16669)------------------------------
% 12.88/2.01  % (16349)Time limit reached!
% 12.88/2.01  % (16349)------------------------------
% 12.88/2.01  % (16349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.01  % (16349)Termination reason: Time limit
% 12.88/2.01  
% 12.88/2.01  % (16349)Memory used [KB]: 22771
% 12.88/2.01  % (16349)Time elapsed: 1.535 s
% 12.88/2.01  % (16349)------------------------------
% 12.88/2.01  % (16349)------------------------------
% 12.88/2.05  % (16356)Time limit reached!
% 12.88/2.05  % (16356)------------------------------
% 12.88/2.05  % (16356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.40/2.06  % (16356)Termination reason: Time limit
% 13.40/2.06  % (16356)Termination phase: Saturation
% 13.40/2.06  
% 13.40/2.06  % (16356)Memory used [KB]: 33133
% 13.40/2.06  % (16356)Time elapsed: 1.600 s
% 13.40/2.06  % (16356)------------------------------
% 13.40/2.06  % (16356)------------------------------
% 14.71/2.25  % (16359)Time limit reached!
% 14.71/2.25  % (16359)------------------------------
% 14.71/2.25  % (16359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.71/2.26  % (16359)Termination reason: Time limit
% 14.71/2.26  
% 14.71/2.26  % (16359)Memory used [KB]: 6524
% 14.71/2.26  % (16359)Time elapsed: 1.807 s
% 14.71/2.26  % (16359)------------------------------
% 14.71/2.26  % (16359)------------------------------
% 14.71/2.29  % (16671)Time limit reached!
% 14.71/2.29  % (16671)------------------------------
% 14.71/2.29  % (16671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.71/2.29  % (16671)Termination reason: Time limit
% 14.71/2.29  % (16671)Termination phase: Saturation
% 14.71/2.29  
% 14.71/2.29  % (16671)Memory used [KB]: 15991
% 14.71/2.29  % (16671)Time elapsed: 0.400 s
% 14.71/2.29  % (16671)------------------------------
% 14.71/2.29  % (16671)------------------------------
% 15.95/2.39  % (16413)Time limit reached!
% 15.95/2.39  % (16413)------------------------------
% 15.95/2.39  % (16413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.95/2.39  % (16413)Termination reason: Time limit
% 15.95/2.39  % (16413)Termination phase: Saturation
% 15.95/2.39  
% 15.95/2.39  % (16413)Memory used [KB]: 25969
% 15.95/2.39  % (16413)Time elapsed: 1.700 s
% 15.95/2.39  % (16413)------------------------------
% 15.95/2.39  % (16413)------------------------------
% 16.37/2.44  % (16351)Time limit reached!
% 16.37/2.44  % (16351)------------------------------
% 16.37/2.44  % (16351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.37/2.44  % (16351)Termination reason: Time limit
% 16.37/2.44  % (16351)Termination phase: Saturation
% 16.37/2.44  
% 16.37/2.44  % (16351)Memory used [KB]: 26865
% 16.37/2.44  % (16351)Time elapsed: 2.0000 s
% 16.37/2.44  % (16351)------------------------------
% 16.37/2.44  % (16351)------------------------------
% 16.37/2.46  % (16590)Time limit reached!
% 16.37/2.46  % (16590)------------------------------
% 16.37/2.46  % (16590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.37/2.47  % (16590)Termination reason: Time limit
% 16.37/2.47  % (16590)Termination phase: Saturation
% 16.37/2.47  
% 16.37/2.47  % (16590)Memory used [KB]: 9722
% 16.37/2.47  % (16590)Time elapsed: 1.300 s
% 16.37/2.47  % (16590)------------------------------
% 16.37/2.47  % (16590)------------------------------
% 16.37/2.47  % (16363)Time limit reached!
% 16.37/2.47  % (16363)------------------------------
% 16.37/2.47  % (16363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.37/2.47  % (16363)Termination reason: Time limit
% 16.37/2.47  
% 16.37/2.47  % (16363)Memory used [KB]: 12665
% 16.37/2.47  % (16363)Time elapsed: 2.021 s
% 16.37/2.47  % (16363)------------------------------
% 16.37/2.47  % (16363)------------------------------
% 17.78/2.65  % (16469)Time limit reached!
% 17.78/2.65  % (16469)------------------------------
% 17.78/2.65  % (16469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.65  % (16469)Termination reason: Time limit
% 17.78/2.65  
% 17.78/2.65  % (16469)Memory used [KB]: 22259
% 17.78/2.65  % (16469)Time elapsed: 1.728 s
% 17.78/2.65  % (16469)------------------------------
% 17.78/2.65  % (16469)------------------------------
% 20.88/3.05  % (16364)Time limit reached!
% 20.88/3.05  % (16364)------------------------------
% 20.88/3.05  % (16364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.88/3.05  % (16364)Termination reason: Time limit
% 20.88/3.05  % (16364)Termination phase: Saturation
% 20.88/3.05  
% 20.88/3.05  % (16364)Memory used [KB]: 31726
% 20.88/3.05  % (16364)Time elapsed: 2.600 s
% 20.88/3.05  % (16364)------------------------------
% 20.88/3.05  % (16364)------------------------------
% 24.45/3.47  % (16358)Time limit reached!
% 24.45/3.47  % (16358)------------------------------
% 24.45/3.47  % (16358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.45/3.47  % (16358)Termination reason: Time limit
% 24.45/3.47  % (16358)Termination phase: Saturation
% 24.45/3.47  
% 24.45/3.47  % (16358)Memory used [KB]: 23794
% 24.45/3.47  % (16358)Time elapsed: 3.0000 s
% 24.45/3.47  % (16358)------------------------------
% 24.45/3.47  % (16358)------------------------------
% 25.65/3.65  % (16412)Time limit reached!
% 25.65/3.65  % (16412)------------------------------
% 25.65/3.65  % (16412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.65/3.65  % (16412)Termination reason: Time limit
% 25.65/3.65  % (16412)Termination phase: Saturation
% 25.65/3.65  
% 25.65/3.65  % (16412)Memory used [KB]: 25074
% 25.65/3.65  % (16412)Time elapsed: 2.800 s
% 25.65/3.65  % (16412)------------------------------
% 25.65/3.65  % (16412)------------------------------
% 31.74/4.34  % (16374)Time limit reached!
% 31.74/4.34  % (16374)------------------------------
% 31.74/4.34  % (16374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.74/4.34  % (16374)Termination reason: Time limit
% 31.74/4.34  % (16374)Termination phase: Saturation
% 31.74/4.34  
% 31.74/4.34  % (16374)Memory used [KB]: 64092
% 31.74/4.34  % (16374)Time elapsed: 3.900 s
% 31.74/4.34  % (16374)------------------------------
% 31.74/4.34  % (16374)------------------------------
% 32.77/4.55  % (16518)Refutation found. Thanks to Tanya!
% 32.77/4.55  % SZS status Theorem for theBenchmark
% 32.77/4.55  % SZS output start Proof for theBenchmark
% 33.46/4.57  fof(f112493,plain,(
% 33.46/4.57    $false),
% 33.46/4.57    inference(global_subsumption,[],[f46144,f81058,f112492])).
% 33.46/4.57  fof(f112492,plain,(
% 33.46/4.57    r1_tarski(sK2,sK0)),
% 33.46/4.57    inference(subsumption_resolution,[],[f112453,f81058])).
% 33.46/4.57  fof(f112453,plain,(
% 33.46/4.57    r1_tarski(sK2,sK0) | sK0 = sK2),
% 33.46/4.57    inference(resolution,[],[f112245,f52149])).
% 33.46/4.57  fof(f52149,plain,(
% 33.46/4.57    ~r2_hidden(sK5(sK2,sK0),sK0) | sK0 = sK2),
% 33.46/4.57    inference(trivial_inequality_removal,[],[f51893])).
% 33.46/4.57  fof(f51893,plain,(
% 33.46/4.57    sK0 != sK0 | ~r2_hidden(sK5(sK2,sK0),sK0) | sK0 = sK2),
% 33.46/4.57    inference(superposition,[],[f69,f46141])).
% 33.46/4.57  fof(f46141,plain,(
% 33.46/4.57    sK0 = k4_xboole_0(sK0,k1_tarski(sK5(sK2,sK0))) | sK0 = sK2),
% 33.46/4.57    inference(resolution,[],[f46140,f236])).
% 33.46/4.57  fof(f236,plain,(
% 33.46/4.57    ( ! [X6,X5] : (~r1_tarski(X5,X6) | k4_xboole_0(X5,k1_tarski(sK5(X6,X5))) = X5 | X5 = X6) )),
% 33.46/4.57    inference(resolution,[],[f139,f59])).
% 33.46/4.57  fof(f59,plain,(
% 33.46/4.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 33.46/4.57    inference(cnf_transformation,[],[f27])).
% 33.46/4.57  fof(f27,plain,(
% 33.46/4.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 33.46/4.57    inference(flattening,[],[f26])).
% 33.46/4.57  fof(f26,plain,(
% 33.46/4.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 33.46/4.57    inference(nnf_transformation,[],[f7])).
% 33.46/4.57  fof(f7,axiom,(
% 33.46/4.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 33.46/4.57  fof(f139,plain,(
% 33.46/4.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | k4_xboole_0(X0,k1_tarski(sK5(X1,X0))) = X0) )),
% 33.46/4.57    inference(resolution,[],[f70,f65])).
% 33.46/4.57  fof(f65,plain,(
% 33.46/4.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 33.46/4.57    inference(cnf_transformation,[],[f33])).
% 33.46/4.57  fof(f33,plain,(
% 33.46/4.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 33.46/4.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 33.46/4.57  fof(f32,plain,(
% 33.46/4.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 33.46/4.57    introduced(choice_axiom,[])).
% 33.46/4.57  fof(f31,plain,(
% 33.46/4.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 33.46/4.57    inference(rectify,[],[f30])).
% 33.46/4.57  fof(f30,plain,(
% 33.46/4.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 33.46/4.57    inference(nnf_transformation,[],[f18])).
% 33.46/4.57  fof(f18,plain,(
% 33.46/4.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 33.46/4.57    inference(ennf_transformation,[],[f2])).
% 33.46/4.57  fof(f2,axiom,(
% 33.46/4.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 33.46/4.57  fof(f70,plain,(
% 33.46/4.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 33.46/4.57    inference(cnf_transformation,[],[f36])).
% 33.46/4.57  fof(f36,plain,(
% 33.46/4.57    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 33.46/4.57    inference(nnf_transformation,[],[f12])).
% 33.46/4.57  fof(f12,axiom,(
% 33.46/4.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 33.46/4.57  fof(f46140,plain,(
% 33.46/4.57    r1_tarski(sK0,sK2)),
% 33.46/4.57    inference(duplicate_literal_removal,[],[f46129])).
% 33.46/4.57  fof(f46129,plain,(
% 33.46/4.57    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)),
% 33.46/4.57    inference(resolution,[],[f45888,f64])).
% 33.46/4.57  fof(f64,plain,(
% 33.46/4.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 33.46/4.57    inference(cnf_transformation,[],[f33])).
% 33.46/4.57  fof(f45888,plain,(
% 33.46/4.57    ( ! [X1] : (~r2_hidden(sK5(X1,sK2),sK0) | r1_tarski(X1,sK2)) )),
% 33.46/4.57    inference(resolution,[],[f45571,f65])).
% 33.46/4.57  fof(f45571,plain,(
% 33.46/4.57    ( ! [X2] : (r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 33.46/4.57    inference(subsumption_resolution,[],[f45313,f118])).
% 33.46/4.57  fof(f118,plain,(
% 33.46/4.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 33.46/4.57    inference(resolution,[],[f117,f54])).
% 33.46/4.57  fof(f54,plain,(
% 33.46/4.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 33.46/4.57    inference(cnf_transformation,[],[f25])).
% 33.46/4.57  fof(f25,plain,(
% 33.46/4.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 33.46/4.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 33.46/4.57  fof(f24,plain,(
% 33.46/4.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 33.46/4.57    introduced(choice_axiom,[])).
% 33.46/4.57  fof(f23,plain,(
% 33.46/4.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 33.46/4.57    inference(rectify,[],[f22])).
% 33.46/4.57  fof(f22,plain,(
% 33.46/4.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 33.46/4.57    inference(nnf_transformation,[],[f1])).
% 33.46/4.57  fof(f1,axiom,(
% 33.46/4.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 33.46/4.57  fof(f117,plain,(
% 33.46/4.57    v1_xboole_0(k1_xboole_0)),
% 33.46/4.57    inference(duplicate_literal_removal,[],[f116])).
% 33.46/4.57  fof(f116,plain,(
% 33.46/4.57    v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 33.46/4.57    inference(resolution,[],[f115,f55])).
% 33.46/4.57  fof(f55,plain,(
% 33.46/4.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 33.46/4.57    inference(cnf_transformation,[],[f25])).
% 33.46/4.57  fof(f115,plain,(
% 33.46/4.57    ( ! [X0] : (~r2_hidden(sK4(X0),k1_xboole_0) | v1_xboole_0(X0)) )),
% 33.46/4.57    inference(superposition,[],[f100,f53])).
% 33.46/4.57  fof(f53,plain,(
% 33.46/4.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 33.46/4.57    inference(cnf_transformation,[],[f9])).
% 33.46/4.57  fof(f9,axiom,(
% 33.46/4.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 33.46/4.57  fof(f100,plain,(
% 33.46/4.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0),k4_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 33.46/4.57    inference(resolution,[],[f92,f55])).
% 33.46/4.57  fof(f92,plain,(
% 33.46/4.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 33.46/4.57    inference(equality_resolution,[],[f74])).
% 33.46/4.57  fof(f74,plain,(
% 33.46/4.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 33.46/4.57    inference(cnf_transformation,[],[f43])).
% 33.46/4.57  fof(f43,plain,(
% 33.46/4.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 33.46/4.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).
% 33.46/4.57  fof(f42,plain,(
% 33.46/4.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 33.46/4.57    introduced(choice_axiom,[])).
% 33.46/4.57  fof(f41,plain,(
% 33.46/4.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 33.46/4.57    inference(rectify,[],[f40])).
% 33.46/4.57  fof(f40,plain,(
% 33.46/4.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 33.46/4.57    inference(flattening,[],[f39])).
% 33.46/4.57  fof(f39,plain,(
% 33.46/4.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 33.46/4.57    inference(nnf_transformation,[],[f4])).
% 33.46/4.57  fof(f4,axiom,(
% 33.46/4.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 33.46/4.57  fof(f45313,plain,(
% 33.46/4.57    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 33.46/4.57    inference(superposition,[],[f91,f45300])).
% 33.46/4.57  fof(f45300,plain,(
% 33.46/4.57    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 33.46/4.57    inference(subsumption_resolution,[],[f45298,f51])).
% 33.46/4.57  fof(f51,plain,(
% 33.46/4.57    k1_xboole_0 != sK1),
% 33.46/4.57    inference(cnf_transformation,[],[f21])).
% 33.46/4.57  fof(f21,plain,(
% 33.46/4.57    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 33.46/4.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).
% 33.46/4.57  fof(f20,plain,(
% 33.46/4.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 33.46/4.57    introduced(choice_axiom,[])).
% 33.46/4.57  fof(f16,plain,(
% 33.46/4.57    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 33.46/4.57    inference(flattening,[],[f15])).
% 33.46/4.57  fof(f15,plain,(
% 33.46/4.57    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 33.46/4.57    inference(ennf_transformation,[],[f14])).
% 33.46/4.57  fof(f14,negated_conjecture,(
% 33.46/4.57    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 33.46/4.57    inference(negated_conjecture,[],[f13])).
% 33.46/4.57  fof(f13,conjecture,(
% 33.46/4.57    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 33.46/4.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 33.46/4.58  fof(f45298,plain,(
% 33.46/4.58    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 33.46/4.58    inference(trivial_inequality_removal,[],[f45281])).
% 33.46/4.58  fof(f45281,plain,(
% 33.46/4.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 33.46/4.58    inference(superposition,[],[f66,f45220])).
% 33.46/4.58  fof(f45220,plain,(
% 33.46/4.58    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 33.46/4.58    inference(superposition,[],[f44264,f264])).
% 33.46/4.58  fof(f264,plain,(
% 33.46/4.58    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 33.46/4.58    inference(resolution,[],[f257,f56])).
% 33.46/4.58  fof(f56,plain,(
% 33.46/4.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 33.46/4.58    inference(cnf_transformation,[],[f17])).
% 33.46/4.58  fof(f17,plain,(
% 33.46/4.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 33.46/4.58    inference(ennf_transformation,[],[f8])).
% 33.46/4.58  fof(f8,axiom,(
% 33.46/4.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 33.46/4.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 33.46/4.58  fof(f257,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 33.46/4.58    inference(duplicate_literal_removal,[],[f248])).
% 33.46/4.58  fof(f248,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 33.46/4.58    inference(resolution,[],[f104,f65])).
% 33.46/4.58  fof(f104,plain,(
% 33.46/4.58    ( ! [X4,X2,X3] : (r2_hidden(sK5(k4_xboole_0(X2,X3),X4),X2) | r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 33.46/4.58    inference(resolution,[],[f93,f64])).
% 33.46/4.58  fof(f93,plain,(
% 33.46/4.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 33.46/4.58    inference(equality_resolution,[],[f73])).
% 33.46/4.58  fof(f73,plain,(
% 33.46/4.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 33.46/4.58    inference(cnf_transformation,[],[f43])).
% 33.46/4.58  fof(f44264,plain,(
% 33.46/4.58    ( ! [X16] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X16,sK2),sK0),sK1)) )),
% 33.46/4.58    inference(superposition,[],[f20503,f20653])).
% 33.46/4.58  fof(f20653,plain,(
% 33.46/4.58    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1))) )),
% 33.46/4.58    inference(superposition,[],[f20557,f49])).
% 33.46/4.58  fof(f49,plain,(
% 33.46/4.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 33.46/4.58    inference(cnf_transformation,[],[f21])).
% 33.46/4.58  fof(f20557,plain,(
% 33.46/4.58    ( ! [X37,X35,X38,X36] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(X36,X38))) )),
% 33.46/4.58    inference(forward_demodulation,[],[f20465,f90])).
% 33.46/4.58  fof(f90,plain,(
% 33.46/4.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 33.46/4.58    inference(equality_resolution,[],[f67])).
% 33.46/4.58  fof(f67,plain,(
% 33.46/4.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 33.46/4.58    inference(cnf_transformation,[],[f35])).
% 33.46/4.58  fof(f35,plain,(
% 33.46/4.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 33.46/4.58    inference(flattening,[],[f34])).
% 33.46/4.58  fof(f34,plain,(
% 33.46/4.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 33.46/4.58    inference(nnf_transformation,[],[f10])).
% 33.46/4.58  fof(f10,axiom,(
% 33.46/4.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 33.46/4.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 33.46/4.58  fof(f20465,plain,(
% 33.46/4.58    ( ! [X37,X35,X38,X36] : (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(X36,X38)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X37,X38))) )),
% 33.46/4.58    inference(superposition,[],[f85,f577])).
% 33.46/4.58  fof(f577,plain,(
% 33.46/4.58    ( ! [X23,X22] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X22,X23),X23)) )),
% 33.46/4.58    inference(resolution,[],[f557,f126])).
% 33.46/4.58  fof(f126,plain,(
% 33.46/4.58    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 33.46/4.58    inference(resolution,[],[f59,f120])).
% 33.46/4.58  fof(f120,plain,(
% 33.46/4.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 33.46/4.58    inference(resolution,[],[f118,f64])).
% 33.46/4.58  fof(f557,plain,(
% 33.46/4.58    ( ! [X12,X13,X11] : (r1_tarski(k3_xboole_0(k4_xboole_0(X11,X12),X12),X13)) )),
% 33.46/4.58    inference(resolution,[],[f546,f64])).
% 33.46/4.58  fof(f546,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k4_xboole_0(X1,X2),X2))) )),
% 33.46/4.58    inference(resolution,[],[f545,f54])).
% 33.46/4.58  fof(f545,plain,(
% 33.46/4.58    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 33.46/4.58    inference(duplicate_literal_removal,[],[f535])).
% 33.46/4.58  fof(f535,plain,(
% 33.46/4.58    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 33.46/4.58    inference(resolution,[],[f156,f111])).
% 33.46/4.58  fof(f111,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 33.46/4.58    inference(resolution,[],[f96,f55])).
% 33.46/4.58  fof(f96,plain,(
% 33.46/4.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 33.46/4.58    inference(equality_resolution,[],[f79])).
% 33.46/4.58  fof(f79,plain,(
% 33.46/4.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 33.46/4.58    inference(cnf_transformation,[],[f48])).
% 33.46/4.58  fof(f48,plain,(
% 33.46/4.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 33.46/4.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).
% 33.46/4.58  fof(f47,plain,(
% 33.46/4.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 33.46/4.58    introduced(choice_axiom,[])).
% 33.46/4.58  fof(f46,plain,(
% 33.46/4.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 33.46/4.58    inference(rectify,[],[f45])).
% 33.46/4.58  fof(f45,plain,(
% 33.46/4.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 33.46/4.58    inference(flattening,[],[f44])).
% 33.46/4.58  fof(f44,plain,(
% 33.46/4.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 33.46/4.58    inference(nnf_transformation,[],[f3])).
% 33.46/4.58  fof(f3,axiom,(
% 33.46/4.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 33.46/4.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 33.46/4.58  fof(f156,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 33.46/4.58    inference(resolution,[],[f107,f92])).
% 33.46/4.58  fof(f107,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 33.46/4.58    inference(resolution,[],[f95,f55])).
% 33.46/4.58  fof(f95,plain,(
% 33.46/4.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 33.46/4.58    inference(equality_resolution,[],[f80])).
% 33.46/4.58  fof(f80,plain,(
% 33.46/4.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 33.46/4.58    inference(cnf_transformation,[],[f48])).
% 33.46/4.58  fof(f85,plain,(
% 33.46/4.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 33.46/4.58    inference(cnf_transformation,[],[f11])).
% 33.46/4.58  fof(f11,axiom,(
% 33.46/4.58    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 33.46/4.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 33.46/4.58  fof(f20503,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 33.46/4.58    inference(superposition,[],[f85,f97])).
% 33.46/4.58  fof(f97,plain,(
% 33.46/4.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 33.46/4.58    inference(resolution,[],[f56,f86])).
% 33.46/4.58  fof(f86,plain,(
% 33.46/4.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 33.46/4.58    inference(equality_resolution,[],[f58])).
% 33.46/4.58  fof(f58,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 33.46/4.58    inference(cnf_transformation,[],[f27])).
% 33.46/4.58  fof(f66,plain,(
% 33.46/4.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 33.46/4.58    inference(cnf_transformation,[],[f35])).
% 33.46/4.58  fof(f91,plain,(
% 33.46/4.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 33.46/4.58    inference(equality_resolution,[],[f75])).
% 33.46/4.58  fof(f75,plain,(
% 33.46/4.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 33.46/4.58    inference(cnf_transformation,[],[f43])).
% 33.46/4.58  fof(f69,plain,(
% 33.46/4.58    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 33.46/4.58    inference(cnf_transformation,[],[f36])).
% 33.46/4.58  fof(f112245,plain,(
% 33.46/4.58    ( ! [X33] : (r2_hidden(sK5(sK2,X33),sK0) | r1_tarski(sK2,X33)) )),
% 33.46/4.58    inference(resolution,[],[f112211,f64])).
% 33.46/4.58  fof(f112211,plain,(
% 33.46/4.58    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 33.46/4.58    inference(condensation,[],[f112167])).
% 33.46/4.58  fof(f112167,plain,(
% 33.46/4.58    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0) | ~r2_hidden(X0,X1)) )),
% 33.46/4.58    inference(resolution,[],[f111944,f91])).
% 33.46/4.58  fof(f111944,plain,(
% 33.46/4.58    ( ! [X218,X219] : (~r2_hidden(X219,k4_xboole_0(X218,sK0)) | ~r2_hidden(X219,sK2)) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f111819,f118])).
% 33.46/4.58  fof(f111819,plain,(
% 33.46/4.58    ( ! [X218,X219] : (r2_hidden(X219,k1_xboole_0) | ~r2_hidden(X219,k4_xboole_0(X218,sK0)) | ~r2_hidden(X219,sK2)) )),
% 33.46/4.58    inference(superposition,[],[f94,f111694])).
% 33.46/4.58  fof(f111694,plain,(
% 33.46/4.58    ( ! [X29] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X29,sK0))) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f111671,f90])).
% 33.46/4.58  fof(f111671,plain,(
% 33.46/4.58    ( ! [X29] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X29,sK0))) )),
% 33.46/4.58    inference(superposition,[],[f93716,f672])).
% 33.46/4.58  fof(f672,plain,(
% 33.46/4.58    ( ! [X23,X22] : (k1_xboole_0 = k3_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 33.46/4.58    inference(resolution,[],[f655,f126])).
% 33.46/4.58  fof(f655,plain,(
% 33.46/4.58    ( ! [X12,X13,X11] : (r1_tarski(k3_xboole_0(X11,k4_xboole_0(X12,X11)),X13)) )),
% 33.46/4.58    inference(resolution,[],[f647,f64])).
% 33.46/4.58  fof(f647,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 33.46/4.58    inference(resolution,[],[f646,f54])).
% 33.46/4.58  fof(f646,plain,(
% 33.46/4.58    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 33.46/4.58    inference(duplicate_literal_removal,[],[f635])).
% 33.46/4.58  fof(f635,plain,(
% 33.46/4.58    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 33.46/4.58    inference(resolution,[],[f195,f107])).
% 33.46/4.58  fof(f195,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 33.46/4.58    inference(resolution,[],[f111,f92])).
% 33.46/4.58  fof(f93716,plain,(
% 33.46/4.58    ( ! [X38] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X38),sK1) | k1_xboole_0 = k3_xboole_0(sK2,X38)) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f93670,f51])).
% 33.46/4.58  fof(f93670,plain,(
% 33.46/4.58    ( ! [X38] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X38),sK1) | k1_xboole_0 = k3_xboole_0(sK2,X38) | k1_xboole_0 = sK1) )),
% 33.46/4.58    inference(superposition,[],[f66,f81151])).
% 33.46/4.58  fof(f81151,plain,(
% 33.46/4.58    ( ! [X27] : (k2_zfmisc_1(k3_xboole_0(sK2,X27),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X27),sK1)) )),
% 33.46/4.58    inference(forward_demodulation,[],[f81128,f20503])).
% 33.46/4.58  fof(f81128,plain,(
% 33.46/4.58    ( ! [X27] : (k2_zfmisc_1(k3_xboole_0(sK2,X27),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X27,sK1))) )),
% 33.46/4.58    inference(superposition,[],[f20503,f80739])).
% 33.46/4.58  fof(f80739,plain,(
% 33.46/4.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 33.46/4.58    inference(superposition,[],[f49,f80726])).
% 33.46/4.58  fof(f80726,plain,(
% 33.46/4.58    sK1 = sK3),
% 33.46/4.58    inference(subsumption_resolution,[],[f80687,f22964])).
% 33.46/4.58  fof(f22964,plain,(
% 33.46/4.58    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 33.46/4.58    inference(resolution,[],[f22960,f59])).
% 33.46/4.58  fof(f22960,plain,(
% 33.46/4.58    r1_tarski(sK1,sK3)),
% 33.46/4.58    inference(duplicate_literal_removal,[],[f22949])).
% 33.46/4.58  fof(f22949,plain,(
% 33.46/4.58    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)),
% 33.46/4.58    inference(resolution,[],[f22721,f64])).
% 33.46/4.58  fof(f22721,plain,(
% 33.46/4.58    ( ! [X1] : (~r2_hidden(sK5(X1,sK3),sK1) | r1_tarski(X1,sK3)) )),
% 33.46/4.58    inference(resolution,[],[f22407,f65])).
% 33.46/4.58  fof(f22407,plain,(
% 33.46/4.58    ( ! [X2] : (r2_hidden(X2,sK3) | ~r2_hidden(X2,sK1)) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f22151,f118])).
% 33.46/4.58  fof(f22151,plain,(
% 33.46/4.58    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK3) | ~r2_hidden(X2,sK1)) )),
% 33.46/4.58    inference(superposition,[],[f91,f22140])).
% 33.46/4.58  fof(f22140,plain,(
% 33.46/4.58    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 33.46/4.58    inference(subsumption_resolution,[],[f22139,f50])).
% 33.46/4.58  fof(f50,plain,(
% 33.46/4.58    k1_xboole_0 != sK0),
% 33.46/4.58    inference(cnf_transformation,[],[f21])).
% 33.46/4.58  fof(f22139,plain,(
% 33.46/4.58    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 33.46/4.58    inference(trivial_inequality_removal,[],[f22127])).
% 33.46/4.58  fof(f22127,plain,(
% 33.46/4.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 33.46/4.58    inference(superposition,[],[f66,f22093])).
% 33.46/4.58  fof(f22093,plain,(
% 33.46/4.58    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 33.46/4.58    inference(superposition,[],[f21377,f264])).
% 33.46/4.58  fof(f21377,plain,(
% 33.46/4.58    ( ! [X10] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X10,sK3),sK1))) )),
% 33.46/4.58    inference(superposition,[],[f20457,f20811])).
% 33.46/4.58  fof(f20811,plain,(
% 33.46/4.58    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 33.46/4.58    inference(superposition,[],[f20603,f49])).
% 33.46/4.58  fof(f20603,plain,(
% 33.46/4.58    ( ! [X37,X35,X38,X36] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X38,X36))) )),
% 33.46/4.58    inference(forward_demodulation,[],[f20511,f89])).
% 33.46/4.58  fof(f89,plain,(
% 33.46/4.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 33.46/4.58    inference(equality_resolution,[],[f68])).
% 33.46/4.58  fof(f68,plain,(
% 33.46/4.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 33.46/4.58    inference(cnf_transformation,[],[f35])).
% 33.46/4.58  fof(f20511,plain,(
% 33.46/4.58    ( ! [X37,X35,X38,X36] : (k3_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X38,X36)) = k2_zfmisc_1(k3_xboole_0(X37,X38),k1_xboole_0)) )),
% 33.46/4.58    inference(superposition,[],[f85,f577])).
% 33.46/4.58  fof(f20457,plain,(
% 33.46/4.58    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 33.46/4.58    inference(superposition,[],[f85,f97])).
% 33.46/4.58  fof(f80687,plain,(
% 33.46/4.58    r1_tarski(sK3,sK1) | sK1 = sK3),
% 33.46/4.58    inference(resolution,[],[f80516,f26613])).
% 33.46/4.58  fof(f26613,plain,(
% 33.46/4.58    ~r2_hidden(sK5(sK3,sK1),sK1) | sK1 = sK3),
% 33.46/4.58    inference(trivial_inequality_removal,[],[f26360])).
% 33.46/4.58  fof(f26360,plain,(
% 33.46/4.58    sK1 != sK1 | ~r2_hidden(sK5(sK3,sK1),sK1) | sK1 = sK3),
% 33.46/4.58    inference(superposition,[],[f69,f22961])).
% 33.46/4.58  fof(f22961,plain,(
% 33.46/4.58    sK1 = k4_xboole_0(sK1,k1_tarski(sK5(sK3,sK1))) | sK1 = sK3),
% 33.46/4.58    inference(resolution,[],[f22960,f236])).
% 33.46/4.58  fof(f80516,plain,(
% 33.46/4.58    ( ! [X32] : (r2_hidden(sK5(sK3,X32),sK1) | r1_tarski(sK3,X32)) )),
% 33.46/4.58    inference(resolution,[],[f80483,f64])).
% 33.46/4.58  fof(f80483,plain,(
% 33.46/4.58    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK1)) )),
% 33.46/4.58    inference(condensation,[],[f80444])).
% 33.46/4.58  fof(f80444,plain,(
% 33.46/4.58    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK1) | ~r2_hidden(X0,X1)) )),
% 33.46/4.58    inference(resolution,[],[f80419,f91])).
% 33.46/4.58  fof(f80419,plain,(
% 33.46/4.58    ( ! [X206,X207] : (~r2_hidden(X207,k4_xboole_0(X206,sK1)) | ~r2_hidden(X207,sK3)) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f80293,f118])).
% 33.46/4.58  fof(f80293,plain,(
% 33.46/4.58    ( ! [X206,X207] : (r2_hidden(X207,k1_xboole_0) | ~r2_hidden(X207,k4_xboole_0(X206,sK1)) | ~r2_hidden(X207,sK3)) )),
% 33.46/4.58    inference(superposition,[],[f94,f80173])).
% 33.46/4.58  fof(f80173,plain,(
% 33.46/4.58    ( ! [X29] : (k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X29,sK1))) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f80150,f89])).
% 33.46/4.58  fof(f80150,plain,(
% 33.46/4.58    ( ! [X29] : (k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X29,sK1))) )),
% 33.46/4.58    inference(superposition,[],[f58910,f672])).
% 33.46/4.58  fof(f58910,plain,(
% 33.46/4.58    ( ! [X22] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X22)) | k1_xboole_0 = k3_xboole_0(sK3,X22)) )),
% 33.46/4.58    inference(subsumption_resolution,[],[f58877,f50])).
% 33.46/4.58  fof(f58877,plain,(
% 33.46/4.58    ( ! [X22] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X22)) | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK3,X22)) )),
% 33.46/4.58    inference(superposition,[],[f66,f46370])).
% 33.46/4.58  fof(f46370,plain,(
% 33.46/4.58    ( ! [X5] : (k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5))) )),
% 33.46/4.58    inference(forward_demodulation,[],[f46352,f20457])).
% 33.46/4.58  fof(f46352,plain,(
% 33.46/4.58    ( ! [X5] : (k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X5))) )),
% 33.46/4.58    inference(superposition,[],[f20457,f46319])).
% 33.46/4.58  fof(f46319,plain,(
% 33.46/4.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 33.46/4.58    inference(subsumption_resolution,[],[f46317,f23077])).
% 33.46/4.58  fof(f23077,plain,(
% 33.46/4.58    ( ! [X43] : (r1_tarski(k2_zfmisc_1(X43,sK1),k2_zfmisc_1(X43,sK3))) )),
% 33.46/4.58    inference(superposition,[],[f21404,f22965])).
% 33.46/4.58  fof(f22965,plain,(
% 33.46/4.58    sK1 = k3_xboole_0(sK1,sK3)),
% 33.46/4.58    inference(resolution,[],[f22960,f56])).
% 33.46/4.58  fof(f21404,plain,(
% 33.46/4.58    ( ! [X92,X93,X91] : (r1_tarski(k2_zfmisc_1(X91,k3_xboole_0(X92,X93)),k2_zfmisc_1(X91,X93))) )),
% 33.46/4.58    inference(superposition,[],[f310,f20457])).
% 33.46/4.58  fof(f310,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 33.46/4.58    inference(duplicate_literal_removal,[],[f298])).
% 33.46/4.58  fof(f298,plain,(
% 33.46/4.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 33.46/4.58    inference(resolution,[],[f108,f65])).
% 33.46/4.58  fof(f108,plain,(
% 33.46/4.58    ( ! [X4,X2,X3] : (r2_hidden(sK5(k3_xboole_0(X2,X3),X4),X3) | r1_tarski(k3_xboole_0(X2,X3),X4)) )),
% 33.46/4.58    inference(resolution,[],[f95,f64])).
% 33.46/4.58  fof(f46317,plain,(
% 33.46/4.58    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 33.46/4.58    inference(resolution,[],[f46207,f59])).
% 33.46/4.58  fof(f46207,plain,(
% 33.46/4.58    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 33.46/4.58    inference(superposition,[],[f44465,f46145])).
% 33.46/4.58  fof(f46145,plain,(
% 33.46/4.58    sK0 = k3_xboole_0(sK0,sK2)),
% 33.46/4.58    inference(resolution,[],[f46140,f56])).
% 33.46/4.58  fof(f44465,plain,(
% 33.46/4.58    ( ! [X14] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X14,sK2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 33.46/4.58    inference(superposition,[],[f44296,f49])).
% 33.46/4.58  fof(f44296,plain,(
% 33.46/4.58    ( ! [X99,X97,X98] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X97,X99),X98),k2_zfmisc_1(X99,X98))) )),
% 33.46/4.58    inference(superposition,[],[f310,f20503])).
% 33.46/4.58  fof(f94,plain,(
% 33.46/4.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 33.46/4.58    inference(equality_resolution,[],[f81])).
% 33.46/4.58  fof(f81,plain,(
% 33.46/4.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 33.46/4.58    inference(cnf_transformation,[],[f48])).
% 33.46/4.58  fof(f81058,plain,(
% 33.46/4.58    sK0 != sK2),
% 33.46/4.58    inference(trivial_inequality_removal,[],[f80740])).
% 33.46/4.58  fof(f80740,plain,(
% 33.46/4.58    sK1 != sK1 | sK0 != sK2),
% 33.46/4.58    inference(superposition,[],[f52,f80726])).
% 33.46/4.58  fof(f52,plain,(
% 33.46/4.58    sK1 != sK3 | sK0 != sK2),
% 33.46/4.58    inference(cnf_transformation,[],[f21])).
% 33.46/4.58  fof(f46144,plain,(
% 33.46/4.58    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 33.46/4.58    inference(resolution,[],[f46140,f59])).
% 33.46/4.58  % SZS output end Proof for theBenchmark
% 33.46/4.58  % (16518)------------------------------
% 33.46/4.58  % (16518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.46/4.58  % (16518)Termination reason: Refutation
% 33.46/4.58  
% 33.46/4.58  % (16518)Memory used [KB]: 85968
% 33.46/4.58  % (16518)Time elapsed: 3.612 s
% 33.46/4.58  % (16518)------------------------------
% 33.46/4.58  % (16518)------------------------------
% 33.46/4.59  % (16344)Success in time 4.218 s
%------------------------------------------------------------------------------
