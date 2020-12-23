%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:33 EST 2020

% Result     : Timeout 57.90s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  187 (4625 expanded)
%              Number of leaves         :   20 (1143 expanded)
%              Depth                    :   63
%              Number of atoms          :  546 (21211 expanded)
%              Number of equality atoms :  176 (4345 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85107,f41617])).

fof(f41617,plain,(
    r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f41610])).

fof(f41610,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f41275,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f41275,plain,(
    ! [X20] :
      ( ~ r2_hidden(sK5(X20,sK2),sK0)
      | r1_tarski(X20,sK2) ) ),
    inference(resolution,[],[f41203,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41203,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f41062,f134])).

fof(f134,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f133,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f133,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k1_xboole_0),X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f112,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),k4_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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

fof(f41062,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f93,f41047])).

fof(f41047,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f41045,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f21])).

fof(f21,plain,
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

fof(f41045,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f41024])).

fof(f41024,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f68,f40959])).

fof(f40959,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f39000,f2008])).

fof(f2008,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(resolution,[],[f2001,f58])).

fof(f58,plain,(
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

fof(f2001,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f1977])).

fof(f1977,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f119,f67])).

fof(f119,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(k4_xboole_0(X7,X8),X9),X7)
      | r1_tarski(k4_xboole_0(X7,X8),X9) ) ),
    inference(resolution,[],[f95,f66])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f39000,plain,(
    ! [X22] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X22,sK2),sK0),sK1) ),
    inference(superposition,[],[f18823,f20773])).

fof(f20773,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f18839,f51])).

fof(f51,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f18839,plain,(
    ! [X24,X23,X21,X22] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,X22),X23),k2_zfmisc_1(X22,X24)) ),
    inference(forward_demodulation,[],[f18819,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f18819,plain,(
    ! [X24,X23,X21,X22] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,X22),X23),k2_zfmisc_1(X22,X24)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X23,X24)) ),
    inference(superposition,[],[f87,f2695])).

fof(f2695,plain,(
    ! [X23,X22] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X22,X23),X23) ),
    inference(resolution,[],[f2680,f795])).

fof(f795,plain,(
    ! [X16] :
      ( r2_hidden(sK6(k1_xboole_0,X16),X16)
      | k1_xboole_0 = X16 ) ),
    inference(resolution,[],[f150,f136])).

fof(f136,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f134,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK7(X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f39])).

fof(f39,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f150,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | r2_hidden(sK6(X1,X2),X2) ) ),
    inference(resolution,[],[f64,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f2680,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k4_xboole_0(X1,X2),X2)) ),
    inference(resolution,[],[f2679,f56])).

fof(f2679,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ),
    inference(duplicate_literal_removal,[],[f2669])).

fof(f2669,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))
      | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ) ),
    inference(resolution,[],[f245,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f98,f57])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f121,f94])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f18823,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f87,f104])).

fof(f104,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f58,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85107,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f85106,f73517])).

fof(f73517,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f73234])).

fof(f73234,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f54,f73232])).

fof(f73232,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f73231,f26329])).

fof(f26329,plain,(
    r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f26322])).

fof(f26322,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f26006,f66])).

fof(f26006,plain,(
    ! [X20] :
      ( ~ r2_hidden(sK5(X20,sK3),sK1)
      | r1_tarski(X20,sK3) ) ),
    inference(resolution,[],[f25940,f67])).

fof(f25940,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f25804,f134])).

fof(f25804,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f93,f25791])).

fof(f25791,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f25790,f52])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f25790,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f25774])).

fof(f25774,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f68,f25744])).

fof(f25744,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f24029,f2008])).

fof(f24029,plain,(
    ! [X12] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X12,sK3),sK1)) ),
    inference(superposition,[],[f18813,f21267])).

fof(f21267,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f18849,f51])).

fof(f18849,plain,(
    ! [X24,X23,X21,X22] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,k4_xboole_0(X21,X22)),k2_zfmisc_1(X24,X22)) ),
    inference(forward_demodulation,[],[f18829,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18829,plain,(
    ! [X24,X23,X21,X22] : k3_xboole_0(k2_zfmisc_1(X23,k4_xboole_0(X21,X22)),k2_zfmisc_1(X24,X22)) = k2_zfmisc_1(k3_xboole_0(X23,X24),k1_xboole_0) ),
    inference(superposition,[],[f87,f2695])).

fof(f18813,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f87,f104])).

fof(f73231,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f73230])).

fof(f73230,plain,
    ( sK1 = sK3
    | sK1 = sK3
    | ~ r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f73215,f64])).

fof(f73215,plain,
    ( ~ r2_xboole_0(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f72813,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72813,plain,
    ( r2_hidden(sK6(sK1,sK3),sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f72796,f26330])).

fof(f26330,plain,
    ( r2_hidden(sK6(sK1,sK3),sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f26329,f150])).

fof(f72796,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1) ) ),
    inference(condensation,[],[f72606])).

fof(f72606,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f72329,f93])).

fof(f72329,plain,(
    ! [X92,X91] :
      ( ~ r2_hidden(X92,k4_xboole_0(X91,sK1))
      | ~ r2_hidden(X92,sK3) ) ),
    inference(subsumption_resolution,[],[f72148,f134])).

fof(f72148,plain,(
    ! [X92,X91] :
      ( r2_hidden(X92,k1_xboole_0)
      | ~ r2_hidden(X92,k4_xboole_0(X91,sK1))
      | ~ r2_hidden(X92,sK3) ) ),
    inference(superposition,[],[f96,f71819])).

fof(f71819,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X1,sK1)) ),
    inference(subsumption_resolution,[],[f71809,f91])).

fof(f71809,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X1,sK1)) ) ),
    inference(superposition,[],[f48821,f3222])).

fof(f3222,plain,(
    ! [X23,X22] : k1_xboole_0 = k3_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(resolution,[],[f3209,f795])).

fof(f3209,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f3206,f56])).

fof(f3206,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(duplicate_literal_removal,[],[f3194])).

fof(f3194,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))
      | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ) ),
    inference(resolution,[],[f354,f121])).

fof(f354,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f126,f94])).

fof(f48821,plain,(
    ! [X26] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X26))
      | k1_xboole_0 = k3_xboole_0(sK3,X26) ) ),
    inference(subsumption_resolution,[],[f48797,f52])).

fof(f48797,plain,(
    ! [X26] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X26))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k3_xboole_0(sK3,X26) ) ),
    inference(superposition,[],[f68,f41894])).

fof(f41894,plain,(
    ! [X5] : k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5)) ),
    inference(forward_demodulation,[],[f41872,f18813])).

fof(f41872,plain,(
    ! [X5] : k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X5)) ),
    inference(superposition,[],[f18813,f41836])).

fof(f41836,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(subsumption_resolution,[],[f41834,f26515])).

fof(f26515,plain,(
    ! [X249] : r1_tarski(k2_zfmisc_1(X249,sK1),k2_zfmisc_1(X249,sK3)) ),
    inference(superposition,[],[f24133,f26334])).

fof(f26334,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f26329,f58])).

fof(f24133,plain,(
    ! [X432,X434,X433] : r1_tarski(k2_zfmisc_1(X432,k3_xboole_0(X433,X434)),k2_zfmisc_1(X432,X434)) ),
    inference(superposition,[],[f2143,f18813])).

fof(f2143,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f2117])).

fof(f2117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f124,f67])).

fof(f124,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(k3_xboole_0(X7,X8),X9),X8)
      | r1_tarski(k3_xboole_0(X7,X8),X9) ) ),
    inference(resolution,[],[f97,f66])).

fof(f41834,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(resolution,[],[f41657,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41657,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f40017,f41622])).

fof(f41622,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f41617,f58])).

fof(f40017,plain,(
    ! [X18] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X18,sK2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f39109,f51])).

fof(f39109,plain,(
    ! [X441,X440,X442] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X440,X442),X441),k2_zfmisc_1(X442,X441)) ),
    inference(superposition,[],[f2143,f18823])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f54,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f85106,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f85091,f64])).

fof(f85091,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f84997,f72])).

fof(f84997,plain,(
    r2_hidden(sK6(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f84725,f73517])).

fof(f84725,plain,
    ( r2_hidden(sK6(sK0,sK2),sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f84696,f41618])).

fof(f41618,plain,
    ( r2_hidden(sK6(sK0,sK2),sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f41617,f150])).

fof(f84696,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(condensation,[],[f84492])).

fof(f84492,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f84188,f93])).

fof(f84188,plain,(
    ! [X94,X93] :
      ( ~ r2_hidden(X94,k4_xboole_0(X93,sK0))
      | ~ r2_hidden(X94,sK2) ) ),
    inference(subsumption_resolution,[],[f84005,f134])).

fof(f84005,plain,(
    ! [X94,X93] :
      ( r2_hidden(X94,k1_xboole_0)
      | ~ r2_hidden(X94,k4_xboole_0(X93,sK0))
      | ~ r2_hidden(X94,sK2) ) ),
    inference(superposition,[],[f96,f83671])).

fof(f83671,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X1,sK0)) ),
    inference(subsumption_resolution,[],[f83658,f92])).

fof(f83658,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X1,sK0)) ) ),
    inference(superposition,[],[f74446,f3222])).

fof(f74446,plain,(
    ! [X45] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X45),sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,X45) ) ),
    inference(subsumption_resolution,[],[f74404,f53])).

fof(f74404,plain,(
    ! [X45] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X45),sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,X45)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f68,f73650])).

fof(f73650,plain,(
    ! [X36] : k2_zfmisc_1(k3_xboole_0(sK2,X36),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X36),sK1) ),
    inference(forward_demodulation,[],[f73622,f18823])).

fof(f73622,plain,(
    ! [X36] : k2_zfmisc_1(k3_xboole_0(sK2,X36),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X36,sK1)) ),
    inference(superposition,[],[f18823,f73233])).

fof(f73233,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(superposition,[],[f51,f73232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:30:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4497)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (4479)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (4489)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (4497)Refutation not found, incomplete strategy% (4497)------------------------------
% 0.22/0.51  % (4497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4497)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4497)Memory used [KB]: 1791
% 0.22/0.51  % (4497)Time elapsed: 0.054 s
% 0.22/0.51  % (4497)------------------------------
% 0.22/0.51  % (4497)------------------------------
% 0.22/0.52  % (4476)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (4480)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (4481)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (4476)Refutation not found, incomplete strategy% (4476)------------------------------
% 0.22/0.52  % (4476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4476)Memory used [KB]: 10746
% 0.22/0.52  % (4476)Time elapsed: 0.103 s
% 0.22/0.52  % (4476)------------------------------
% 0.22/0.52  % (4476)------------------------------
% 0.22/0.52  % (4492)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (4486)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (4477)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (4496)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (4498)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (4474)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (4474)Refutation not found, incomplete strategy% (4474)------------------------------
% 1.35/0.54  % (4474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (4474)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (4474)Memory used [KB]: 1663
% 1.35/0.54  % (4474)Time elapsed: 0.126 s
% 1.35/0.54  % (4474)------------------------------
% 1.35/0.54  % (4474)------------------------------
% 1.35/0.55  % (4501)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (4490)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.55  % (4503)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (4482)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (4493)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.55  % (4488)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.55  % (4495)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.55  % (4482)Refutation not found, incomplete strategy% (4482)------------------------------
% 1.51/0.55  % (4482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (4482)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (4482)Memory used [KB]: 10746
% 1.51/0.55  % (4482)Time elapsed: 0.139 s
% 1.51/0.55  % (4482)------------------------------
% 1.51/0.55  % (4482)------------------------------
% 1.51/0.55  % (4495)Refutation not found, incomplete strategy% (4495)------------------------------
% 1.51/0.55  % (4495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (4495)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (4495)Memory used [KB]: 1791
% 1.51/0.55  % (4495)Time elapsed: 0.141 s
% 1.51/0.55  % (4495)------------------------------
% 1.51/0.55  % (4495)------------------------------
% 1.51/0.56  % (4485)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (4496)Refutation not found, incomplete strategy% (4496)------------------------------
% 1.51/0.56  % (4496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (4496)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (4496)Memory used [KB]: 10746
% 1.51/0.56  % (4496)Time elapsed: 0.151 s
% 1.51/0.56  % (4496)------------------------------
% 1.51/0.56  % (4496)------------------------------
% 1.51/0.56  % (4487)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.57  % (4475)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.57  % (4484)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.57  % (4494)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.57  % (4494)Refutation not found, incomplete strategy% (4494)------------------------------
% 1.51/0.57  % (4494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (4499)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.58  % (4494)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (4494)Memory used [KB]: 10746
% 1.51/0.58  % (4494)Time elapsed: 0.134 s
% 1.51/0.58  % (4494)------------------------------
% 1.51/0.58  % (4494)------------------------------
% 1.51/0.58  % (4491)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.59  % (4502)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.59  % (4500)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.59  % (4483)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.28/0.68  % (4507)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.28/0.68  % (4507)Refutation not found, incomplete strategy% (4507)------------------------------
% 2.28/0.68  % (4507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (4507)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (4507)Memory used [KB]: 6268
% 2.28/0.68  % (4507)Time elapsed: 0.109 s
% 2.28/0.68  % (4507)------------------------------
% 2.28/0.68  % (4507)------------------------------
% 2.28/0.70  % (4508)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.28/0.71  % (4522)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.28/0.72  % (4509)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.28/0.73  % (4511)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.71/0.76  % (4512)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.88/0.78  % (4515)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.88/0.81  % (4479)Time limit reached!
% 2.88/0.81  % (4479)------------------------------
% 2.88/0.81  % (4479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.81  % (4479)Termination reason: Time limit
% 2.88/0.81  % (4479)Termination phase: Saturation
% 2.88/0.81  
% 2.88/0.81  % (4479)Memory used [KB]: 8571
% 2.88/0.81  % (4479)Time elapsed: 0.400 s
% 2.88/0.81  % (4479)------------------------------
% 2.88/0.81  % (4479)------------------------------
% 3.43/0.87  % (4538)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.43/0.91  % (4486)Time limit reached!
% 3.43/0.91  % (4486)------------------------------
% 3.43/0.91  % (4486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.91  % (4486)Termination reason: Time limit
% 3.43/0.91  
% 3.43/0.91  % (4486)Memory used [KB]: 7803
% 3.43/0.91  % (4486)Time elapsed: 0.500 s
% 3.43/0.91  % (4486)------------------------------
% 3.43/0.91  % (4486)------------------------------
% 3.43/0.92  % (4475)Time limit reached!
% 3.43/0.92  % (4475)------------------------------
% 3.43/0.92  % (4475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.92  % (4475)Termination reason: Time limit
% 3.43/0.92  
% 3.43/0.92  % (4475)Memory used [KB]: 6908
% 3.43/0.92  % (4475)Time elapsed: 0.506 s
% 3.43/0.92  % (4475)------------------------------
% 3.43/0.92  % (4475)------------------------------
% 3.43/0.92  % (4491)Time limit reached!
% 3.43/0.92  % (4491)------------------------------
% 3.43/0.92  % (4491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (4491)Termination reason: Time limit
% 3.83/0.92  
% 3.83/0.92  % (4491)Memory used [KB]: 12537
% 3.83/0.92  % (4491)Time elapsed: 0.512 s
% 3.83/0.92  % (4491)------------------------------
% 3.83/0.92  % (4491)------------------------------
% 3.83/0.94  % (4484)Time limit reached!
% 3.83/0.94  % (4484)------------------------------
% 3.83/0.94  % (4484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.94  % (4484)Termination reason: Time limit
% 3.83/0.94  % (4484)Termination phase: Saturation
% 3.83/0.94  
% 3.83/0.94  % (4484)Memory used [KB]: 17270
% 3.83/0.94  % (4484)Time elapsed: 0.502 s
% 3.83/0.94  % (4484)------------------------------
% 3.83/0.94  % (4484)------------------------------
% 4.08/0.97  % (4539)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.08/1.00  % (4511)Time limit reached!
% 4.08/1.00  % (4511)------------------------------
% 4.08/1.00  % (4511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.00  % (4511)Termination reason: Time limit
% 4.08/1.00  
% 4.08/1.00  % (4511)Memory used [KB]: 6780
% 4.08/1.00  % (4511)Time elapsed: 0.416 s
% 4.08/1.00  % (4511)------------------------------
% 4.08/1.00  % (4511)------------------------------
% 4.08/1.03  % (4490)Time limit reached!
% 4.08/1.03  % (4490)------------------------------
% 4.08/1.03  % (4490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.03  % (4490)Termination reason: Time limit
% 4.08/1.03  
% 4.08/1.03  % (4490)Memory used [KB]: 15223
% 4.08/1.03  % (4490)Time elapsed: 0.619 s
% 4.08/1.03  % (4490)------------------------------
% 4.08/1.03  % (4490)------------------------------
% 4.08/1.03  % (4512)Time limit reached!
% 4.08/1.03  % (4512)------------------------------
% 4.08/1.03  % (4512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.03  % (4512)Termination reason: Time limit
% 4.08/1.03  % (4512)Termination phase: Saturation
% 4.08/1.03  
% 4.08/1.03  % (4512)Memory used [KB]: 12792
% 4.08/1.03  % (4512)Time elapsed: 0.400 s
% 4.08/1.03  % (4512)------------------------------
% 4.08/1.03  % (4512)------------------------------
% 4.08/1.04  % (4541)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.08/1.04  % (4502)Time limit reached!
% 4.08/1.04  % (4502)------------------------------
% 4.08/1.04  % (4502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.04  % (4502)Termination reason: Time limit
% 4.08/1.04  
% 4.08/1.04  % (4502)Memory used [KB]: 7547
% 4.08/1.04  % (4502)Time elapsed: 0.610 s
% 4.08/1.04  % (4502)------------------------------
% 4.08/1.04  % (4502)------------------------------
% 4.67/1.08  % (4481)Time limit reached!
% 4.67/1.08  % (4481)------------------------------
% 4.67/1.08  % (4481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.67/1.08  % (4481)Termination reason: Time limit
% 5.61/1.10  
% 5.61/1.10  % (4481)Memory used [KB]: 9978
% 5.61/1.10  % (4481)Time elapsed: 0.629 s
% 5.61/1.10  % (4481)------------------------------
% 5.61/1.10  % (4481)------------------------------
% 5.61/1.10  % (4544)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.61/1.14  % (4542)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.61/1.14  % (4542)Refutation not found, incomplete strategy% (4542)------------------------------
% 5.61/1.14  % (4542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.14  % (4542)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.14  
% 5.61/1.14  % (4542)Memory used [KB]: 6268
% 5.61/1.14  % (4542)Time elapsed: 0.176 s
% 5.61/1.14  % (4542)------------------------------
% 5.61/1.14  % (4542)------------------------------
% 5.61/1.14  % (4543)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.61/1.14  % (4543)Refutation not found, incomplete strategy% (4543)------------------------------
% 5.61/1.14  % (4543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.14  % (4543)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.14  
% 5.61/1.14  % (4543)Memory used [KB]: 1791
% 5.61/1.14  % (4543)Time elapsed: 0.169 s
% 5.61/1.14  % (4543)------------------------------
% 5.61/1.14  % (4543)------------------------------
% 6.13/1.16  % (4545)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.13/1.16  % (4547)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.13/1.17  % (4545)Refutation not found, incomplete strategy% (4545)------------------------------
% 6.13/1.17  % (4545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.32/1.17  % (4549)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.32/1.18  % (4545)Termination reason: Refutation not found, incomplete strategy
% 6.32/1.18  
% 6.32/1.18  % (4545)Memory used [KB]: 1663
% 6.32/1.18  % (4545)Time elapsed: 0.147 s
% 6.32/1.18  % (4545)------------------------------
% 6.32/1.18  % (4545)------------------------------
% 6.32/1.18  % (4547)Refutation not found, incomplete strategy% (4547)------------------------------
% 6.32/1.18  % (4547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.32/1.18  % (4546)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.32/1.19  % (4548)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.32/1.19  % (4547)Termination reason: Refutation not found, incomplete strategy
% 6.32/1.19  
% 6.32/1.19  % (4547)Memory used [KB]: 6268
% 6.32/1.19  % (4547)Time elapsed: 0.122 s
% 6.32/1.19  % (4547)------------------------------
% 6.32/1.19  % (4547)------------------------------
% 6.81/1.28  % (4551)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.81/1.29  % (4550)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.81/1.29  % (4552)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.33/1.33  % (4553)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.17/1.47  % (4548)Time limit reached!
% 8.17/1.47  % (4548)------------------------------
% 8.17/1.47  % (4548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.47  % (4548)Termination reason: Time limit
% 8.17/1.47  
% 8.17/1.47  % (4548)Memory used [KB]: 4221
% 8.17/1.47  % (4548)Time elapsed: 0.406 s
% 8.17/1.47  % (4548)------------------------------
% 8.17/1.47  % (4548)------------------------------
% 8.87/1.56  % (4544)Time limit reached!
% 8.87/1.56  % (4544)------------------------------
% 8.87/1.56  % (4544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.87/1.56  % (4544)Termination reason: Time limit
% 8.87/1.56  
% 8.87/1.56  % (4544)Memory used [KB]: 3326
% 8.87/1.56  % (4544)Time elapsed: 0.522 s
% 8.87/1.56  % (4544)------------------------------
% 8.87/1.56  % (4544)------------------------------
% 8.87/1.56  % (4551)Time limit reached!
% 8.87/1.56  % (4551)------------------------------
% 8.87/1.56  % (4551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.87/1.57  % (4689)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 8.87/1.57  % (4551)Termination reason: Time limit
% 8.87/1.57  
% 8.87/1.57  % (4551)Memory used [KB]: 2558
% 8.87/1.57  % (4551)Time elapsed: 0.408 s
% 8.87/1.57  % (4551)------------------------------
% 8.87/1.57  % (4551)------------------------------
% 9.98/1.67  % (4500)Time limit reached!
% 9.98/1.67  % (4500)------------------------------
% 9.98/1.67  % (4500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.98/1.68  % (4500)Termination reason: Time limit
% 9.98/1.68  
% 9.98/1.68  % (4500)Memory used [KB]: 22387
% 9.98/1.68  % (4500)Time elapsed: 1.243 s
% 9.98/1.68  % (4500)------------------------------
% 9.98/1.68  % (4500)------------------------------
% 10.37/1.70  % (4709)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.37/1.70  % (4711)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.37/1.75  % (4498)Time limit reached!
% 10.37/1.75  % (4498)------------------------------
% 10.37/1.75  % (4498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.00/1.77  % (4498)Termination reason: Time limit
% 11.00/1.77  
% 11.00/1.77  % (4498)Memory used [KB]: 19317
% 11.00/1.77  % (4498)Time elapsed: 1.325 s
% 11.00/1.77  % (4498)------------------------------
% 11.00/1.77  % (4498)------------------------------
% 11.12/1.77  % (4489)Time limit reached!
% 11.12/1.77  % (4489)------------------------------
% 11.12/1.77  % (4489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.12/1.77  % (4489)Termination reason: Time limit
% 11.12/1.77  % (4489)Termination phase: Saturation
% 11.12/1.77  
% 11.12/1.77  % (4489)Memory used [KB]: 14711
% 11.12/1.77  % (4489)Time elapsed: 1.300 s
% 11.12/1.77  % (4489)------------------------------
% 11.12/1.77  % (4489)------------------------------
% 11.12/1.79  % (4741)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.12/1.81  % (4741)Refutation not found, incomplete strategy% (4741)------------------------------
% 11.12/1.81  % (4741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.12/1.81  % (4741)Termination reason: Refutation not found, incomplete strategy
% 11.12/1.81  
% 11.12/1.81  % (4741)Memory used [KB]: 6268
% 11.12/1.81  % (4741)Time elapsed: 0.078 s
% 11.12/1.81  % (4741)------------------------------
% 11.12/1.81  % (4741)------------------------------
% 11.66/1.88  % (4781)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.66/1.90  % (4522)Time limit reached!
% 11.66/1.90  % (4522)------------------------------
% 11.66/1.90  % (4522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.90  % (4522)Termination reason: Time limit
% 11.66/1.90  
% 11.66/1.90  % (4522)Memory used [KB]: 12920
% 11.66/1.90  % (4522)Time elapsed: 1.217 s
% 11.66/1.90  % (4522)------------------------------
% 11.66/1.90  % (4522)------------------------------
% 11.66/1.91  % (4501)Time limit reached!
% 11.66/1.91  % (4501)------------------------------
% 11.66/1.91  % (4501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.91  % (4501)Termination reason: Time limit
% 11.66/1.91  
% 11.66/1.91  % (4501)Memory used [KB]: 15991
% 11.66/1.91  % (4501)Time elapsed: 1.501 s
% 11.66/1.91  % (4501)------------------------------
% 11.66/1.91  % (4501)------------------------------
% 12.30/1.93  % (4786)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.30/1.93  % (4786)Refutation not found, incomplete strategy% (4786)------------------------------
% 12.30/1.93  % (4786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.30/1.93  % (4786)Termination reason: Refutation not found, incomplete strategy
% 12.30/1.93  
% 12.30/1.93  % (4786)Memory used [KB]: 10746
% 12.30/1.93  % (4786)Time elapsed: 0.102 s
% 12.30/1.93  % (4786)------------------------------
% 12.30/1.93  % (4786)------------------------------
% 12.30/1.98  % (4478)Time limit reached!
% 12.30/1.98  % (4478)------------------------------
% 12.30/1.98  % (4478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.30/1.98  % (4478)Termination reason: Time limit
% 12.30/1.98  
% 12.30/1.98  % (4478)Memory used [KB]: 22771
% 12.30/1.98  % (4478)Time elapsed: 1.525 s
% 12.30/1.98  % (4478)------------------------------
% 12.30/1.98  % (4478)------------------------------
% 12.76/1.99  % (4711)Time limit reached!
% 12.76/1.99  % (4711)------------------------------
% 12.76/1.99  % (4711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/1.99  % (4711)Termination reason: Time limit
% 12.76/1.99  
% 12.76/1.99  % (4711)Memory used [KB]: 9210
% 12.76/1.99  % (4711)Time elapsed: 0.408 s
% 12.76/1.99  % (4711)------------------------------
% 12.76/1.99  % (4711)------------------------------
% 12.76/2.04  % (4485)Time limit reached!
% 12.76/2.04  % (4485)------------------------------
% 12.76/2.04  % (4485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.36/2.06  % (4485)Termination reason: Time limit
% 13.36/2.06  
% 13.36/2.06  % (4485)Memory used [KB]: 28528
% 13.36/2.06  % (4485)Time elapsed: 1.615 s
% 13.36/2.06  % (4485)------------------------------
% 13.36/2.06  % (4485)------------------------------
% 14.13/2.21  % (4781)Time limit reached!
% 14.13/2.21  % (4781)------------------------------
% 14.13/2.21  % (4781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.13/2.21  % (4781)Termination reason: Time limit
% 14.13/2.21  % (4781)Termination phase: Saturation
% 14.13/2.21  
% 14.13/2.21  % (4781)Memory used [KB]: 15095
% 14.13/2.21  % (4781)Time elapsed: 0.400 s
% 14.13/2.21  % (4781)------------------------------
% 14.13/2.21  % (4781)------------------------------
% 14.13/2.23  % (4488)Time limit reached!
% 14.13/2.23  % (4488)------------------------------
% 14.13/2.23  % (4488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.13/2.23  % (4488)Termination reason: Time limit
% 14.13/2.23  % (4488)Termination phase: Saturation
% 14.13/2.23  
% 14.13/2.23  % (4488)Memory used [KB]: 5884
% 14.13/2.23  % (4488)Time elapsed: 1.800 s
% 14.13/2.23  % (4488)------------------------------
% 14.13/2.23  % (4488)------------------------------
% 15.34/2.29  % (4509)Time limit reached!
% 15.34/2.29  % (4509)------------------------------
% 15.34/2.29  % (4509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.34/2.31  % (4509)Termination reason: Time limit
% 15.34/2.31  % (4509)Termination phase: Saturation
% 15.34/2.31  
% 15.34/2.31  % (4509)Memory used [KB]: 22771
% 15.34/2.31  % (4509)Time elapsed: 1.700 s
% 15.34/2.31  % (4509)------------------------------
% 15.34/2.31  % (4509)------------------------------
% 16.27/2.41  % (4492)Time limit reached!
% 16.27/2.41  % (4492)------------------------------
% 16.27/2.41  % (4492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.27/2.41  % (4492)Termination reason: Time limit
% 16.27/2.41  % (4492)Termination phase: Saturation
% 16.27/2.41  
% 16.27/2.41  % (4492)Memory used [KB]: 13048
% 16.27/2.41  % (4492)Time elapsed: 2.0000 s
% 16.27/2.41  % (4492)------------------------------
% 16.27/2.41  % (4492)------------------------------
% 16.27/2.42  % (4480)Time limit reached!
% 16.27/2.42  % (4480)------------------------------
% 16.27/2.42  % (4480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.27/2.42  % (4480)Termination reason: Time limit
% 16.27/2.42  % (4480)Termination phase: Saturation
% 16.27/2.42  
% 16.27/2.42  % (4480)Memory used [KB]: 24818
% 16.27/2.42  % (4480)Time elapsed: 2.0000 s
% 16.27/2.42  % (4480)------------------------------
% 16.27/2.42  % (4480)------------------------------
% 16.57/2.48  % (4550)Time limit reached!
% 16.57/2.48  % (4550)------------------------------
% 16.57/2.48  % (4550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.57/2.48  % (4550)Termination reason: Time limit
% 16.57/2.48  % (4550)Termination phase: Saturation
% 16.57/2.48  
% 16.57/2.48  % (4550)Memory used [KB]: 9722
% 16.57/2.48  % (4550)Time elapsed: 1.300 s
% 16.57/2.48  % (4550)------------------------------
% 16.57/2.48  % (4550)------------------------------
% 17.29/2.57  % (4539)Time limit reached!
% 17.29/2.57  % (4539)------------------------------
% 17.29/2.57  % (4539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.29/2.58  % (4539)Termination reason: Time limit
% 17.29/2.58  % (4539)Termination phase: Saturation
% 17.29/2.58  
% 17.29/2.58  % (4539)Memory used [KB]: 25969
% 17.29/2.58  % (4539)Time elapsed: 1.700 s
% 17.29/2.58  % (4539)------------------------------
% 17.29/2.58  % (4539)------------------------------
% 21.11/3.01  % (4493)Time limit reached!
% 21.11/3.01  % (4493)------------------------------
% 21.11/3.01  % (4493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.11/3.02  % (4493)Termination reason: Time limit
% 21.11/3.02  
% 21.11/3.02  % (4493)Memory used [KB]: 44775
% 21.11/3.02  % (4493)Time elapsed: 2.604 s
% 21.11/3.02  % (4493)------------------------------
% 21.11/3.02  % (4493)------------------------------
% 24.54/3.44  % (4487)Time limit reached!
% 24.54/3.44  % (4487)------------------------------
% 24.54/3.44  % (4487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.54/3.44  % (4487)Termination reason: Time limit
% 24.54/3.44  
% 24.54/3.44  % (4487)Memory used [KB]: 18805
% 24.54/3.44  % (4487)Time elapsed: 3.030 s
% 24.54/3.44  % (4487)------------------------------
% 24.54/3.44  % (4487)------------------------------
% 24.89/3.50  % (4508)Time limit reached!
% 24.89/3.50  % (4508)------------------------------
% 24.89/3.50  % (4508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.89/3.51  % (4508)Termination reason: Time limit
% 24.89/3.51  % (4508)Termination phase: Saturation
% 24.89/3.51  
% 24.89/3.51  % (4508)Memory used [KB]: 23027
% 24.89/3.51  % (4508)Time elapsed: 2.800 s
% 24.89/3.51  % (4508)------------------------------
% 24.89/3.51  % (4508)------------------------------
% 31.65/4.35  % (4503)Time limit reached!
% 31.65/4.35  % (4503)------------------------------
% 31.65/4.35  % (4503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.65/4.35  % (4503)Termination reason: Time limit
% 31.65/4.35  % (4503)Termination phase: Saturation
% 31.65/4.35  
% 31.65/4.35  % (4503)Memory used [KB]: 64860
% 31.65/4.35  % (4503)Time elapsed: 3.900 s
% 31.65/4.35  % (4503)------------------------------
% 31.65/4.35  % (4503)------------------------------
% 33.39/4.55  % (4546)Time limit reached!
% 33.39/4.55  % (4546)------------------------------
% 33.39/4.55  % (4546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.39/4.55  % (4546)Termination reason: Time limit
% 33.39/4.55  % (4546)Termination phase: Saturation
% 33.39/4.55  
% 33.39/4.55  % (4546)Memory used [KB]: 82898
% 33.39/4.55  % (4546)Time elapsed: 3.500 s
% 33.39/4.55  % (4546)------------------------------
% 33.39/4.55  % (4546)------------------------------
% 36.86/5.02  % (4483)Time limit reached!
% 36.86/5.02  % (4483)------------------------------
% 36.86/5.02  % (4483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.86/5.02  % (4483)Termination reason: Time limit
% 36.86/5.02  % (4483)Termination phase: Saturation
% 36.86/5.02  
% 36.86/5.02  % (4483)Memory used [KB]: 49252
% 36.86/5.02  % (4483)Time elapsed: 4.600 s
% 36.86/5.02  % (4483)------------------------------
% 36.86/5.02  % (4483)------------------------------
% 41.73/5.65  % (4477)Time limit reached!
% 41.73/5.65  % (4477)------------------------------
% 41.73/5.65  % (4477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.73/5.65  % (4477)Termination reason: Time limit
% 41.73/5.65  
% 41.73/5.65  % (4477)Memory used [KB]: 68570
% 41.73/5.65  % (4477)Time elapsed: 5.233 s
% 41.73/5.65  % (4477)------------------------------
% 41.73/5.65  % (4477)------------------------------
% 47.07/6.27  % (4538)Time limit reached!
% 47.07/6.27  % (4538)------------------------------
% 47.07/6.27  % (4538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 47.07/6.27  % (4538)Termination reason: Time limit
% 47.07/6.27  % (4538)Termination phase: Saturation
% 47.07/6.27  
% 47.07/6.27  % (4538)Memory used [KB]: 72791
% 47.07/6.27  % (4538)Time elapsed: 5.500 s
% 47.07/6.27  % (4538)------------------------------
% 47.07/6.27  % (4538)------------------------------
% 53.65/7.10  % (4552)Time limit reached!
% 53.65/7.10  % (4552)------------------------------
% 53.65/7.10  % (4552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 53.65/7.10  % (4552)Termination reason: Time limit
% 53.65/7.10  % (4552)Termination phase: Saturation
% 53.65/7.10  
% 53.65/7.10  % (4552)Memory used [KB]: 138291
% 53.65/7.10  % (4552)Time elapsed: 5.900 s
% 53.65/7.10  % (4552)------------------------------
% 53.65/7.10  % (4552)------------------------------
% 57.90/7.73  % (4541)Refutation found. Thanks to Tanya!
% 57.90/7.73  % SZS status Theorem for theBenchmark
% 57.90/7.73  % SZS output start Proof for theBenchmark
% 57.90/7.73  fof(f85108,plain,(
% 57.90/7.73    $false),
% 57.90/7.73    inference(subsumption_resolution,[],[f85107,f41617])).
% 57.90/7.73  fof(f41617,plain,(
% 57.90/7.73    r1_tarski(sK0,sK2)),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f41610])).
% 57.90/7.73  fof(f41610,plain,(
% 57.90/7.73    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)),
% 57.90/7.73    inference(resolution,[],[f41275,f66])).
% 57.90/7.73  fof(f66,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f34])).
% 57.90/7.73  fof(f34,plain,(
% 57.90/7.73    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 57.90/7.73  fof(f33,plain,(
% 57.90/7.73    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f32,plain,(
% 57.90/7.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 57.90/7.73    inference(rectify,[],[f31])).
% 57.90/7.73  fof(f31,plain,(
% 57.90/7.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 57.90/7.73    inference(nnf_transformation,[],[f18])).
% 57.90/7.73  fof(f18,plain,(
% 57.90/7.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 57.90/7.73    inference(ennf_transformation,[],[f2])).
% 57.90/7.73  fof(f2,axiom,(
% 57.90/7.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 57.90/7.73  fof(f41275,plain,(
% 57.90/7.73    ( ! [X20] : (~r2_hidden(sK5(X20,sK2),sK0) | r1_tarski(X20,sK2)) )),
% 57.90/7.73    inference(resolution,[],[f41203,f67])).
% 57.90/7.73  fof(f67,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f34])).
% 57.90/7.73  fof(f41203,plain,(
% 57.90/7.73    ( ! [X2] : (r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f41062,f134])).
% 57.90/7.73  fof(f134,plain,(
% 57.90/7.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 57.90/7.73    inference(resolution,[],[f133,f56])).
% 57.90/7.73  fof(f56,plain,(
% 57.90/7.73    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f26])).
% 57.90/7.73  fof(f26,plain,(
% 57.90/7.73    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 57.90/7.73  fof(f25,plain,(
% 57.90/7.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f24,plain,(
% 57.90/7.73    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 57.90/7.73    inference(rectify,[],[f23])).
% 57.90/7.73  fof(f23,plain,(
% 57.90/7.73    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 57.90/7.73    inference(nnf_transformation,[],[f1])).
% 57.90/7.73  fof(f1,axiom,(
% 57.90/7.73    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 57.90/7.73  fof(f133,plain,(
% 57.90/7.73    v1_xboole_0(k1_xboole_0)),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f132])).
% 57.90/7.73  fof(f132,plain,(
% 57.90/7.73    v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 57.90/7.73    inference(resolution,[],[f131,f57])).
% 57.90/7.73  fof(f57,plain,(
% 57.90/7.73    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f26])).
% 57.90/7.73  fof(f131,plain,(
% 57.90/7.73    ( ! [X0] : (~r2_hidden(sK4(k1_xboole_0),X0) | v1_xboole_0(k1_xboole_0)) )),
% 57.90/7.73    inference(superposition,[],[f112,f55])).
% 57.90/7.73  fof(f55,plain,(
% 57.90/7.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 57.90/7.73    inference(cnf_transformation,[],[f9])).
% 57.90/7.73  fof(f9,axiom,(
% 57.90/7.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 57.90/7.73  fof(f112,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(sK4(X0),k4_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 57.90/7.73    inference(resolution,[],[f94,f57])).
% 57.90/7.73  fof(f94,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 57.90/7.73    inference(equality_resolution,[],[f76])).
% 57.90/7.73  fof(f76,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f45])).
% 57.90/7.73  fof(f45,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).
% 57.90/7.73  fof(f44,plain,(
% 57.90/7.73    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f43,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(rectify,[],[f42])).
% 57.90/7.73  fof(f42,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(flattening,[],[f41])).
% 57.90/7.73  fof(f41,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(nnf_transformation,[],[f4])).
% 57.90/7.73  fof(f4,axiom,(
% 57.90/7.73    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 57.90/7.73  fof(f41062,plain,(
% 57.90/7.73    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 57.90/7.73    inference(superposition,[],[f93,f41047])).
% 57.90/7.73  fof(f41047,plain,(
% 57.90/7.73    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 57.90/7.73    inference(subsumption_resolution,[],[f41045,f53])).
% 57.90/7.73  fof(f53,plain,(
% 57.90/7.73    k1_xboole_0 != sK1),
% 57.90/7.73    inference(cnf_transformation,[],[f22])).
% 57.90/7.73  fof(f22,plain,(
% 57.90/7.73    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f21])).
% 57.90/7.73  fof(f21,plain,(
% 57.90/7.73    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f16,plain,(
% 57.90/7.73    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 57.90/7.73    inference(flattening,[],[f15])).
% 57.90/7.73  fof(f15,plain,(
% 57.90/7.73    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 57.90/7.73    inference(ennf_transformation,[],[f14])).
% 57.90/7.73  fof(f14,negated_conjecture,(
% 57.90/7.73    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 57.90/7.73    inference(negated_conjecture,[],[f13])).
% 57.90/7.73  fof(f13,conjecture,(
% 57.90/7.73    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 57.90/7.73  fof(f41045,plain,(
% 57.90/7.73    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 57.90/7.73    inference(trivial_inequality_removal,[],[f41024])).
% 57.90/7.73  fof(f41024,plain,(
% 57.90/7.73    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 57.90/7.73    inference(superposition,[],[f68,f40959])).
% 57.90/7.73  fof(f40959,plain,(
% 57.90/7.73    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 57.90/7.73    inference(superposition,[],[f39000,f2008])).
% 57.90/7.73  fof(f2008,plain,(
% 57.90/7.73    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 57.90/7.73    inference(resolution,[],[f2001,f58])).
% 57.90/7.73  fof(f58,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 57.90/7.73    inference(cnf_transformation,[],[f17])).
% 57.90/7.73  fof(f17,plain,(
% 57.90/7.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 57.90/7.73    inference(ennf_transformation,[],[f8])).
% 57.90/7.73  fof(f8,axiom,(
% 57.90/7.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 57.90/7.73  fof(f2001,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f1977])).
% 57.90/7.73  fof(f1977,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 57.90/7.73    inference(resolution,[],[f119,f67])).
% 57.90/7.73  fof(f119,plain,(
% 57.90/7.73    ( ! [X8,X7,X9] : (r2_hidden(sK5(k4_xboole_0(X7,X8),X9),X7) | r1_tarski(k4_xboole_0(X7,X8),X9)) )),
% 57.90/7.73    inference(resolution,[],[f95,f66])).
% 57.90/7.73  fof(f95,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 57.90/7.73    inference(equality_resolution,[],[f75])).
% 57.90/7.73  fof(f75,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f45])).
% 57.90/7.73  fof(f39000,plain,(
% 57.90/7.73    ( ! [X22] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X22,sK2),sK0),sK1)) )),
% 57.90/7.73    inference(superposition,[],[f18823,f20773])).
% 57.90/7.73  fof(f20773,plain,(
% 57.90/7.73    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1))) )),
% 57.90/7.73    inference(superposition,[],[f18839,f51])).
% 57.90/7.73  fof(f51,plain,(
% 57.90/7.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 57.90/7.73    inference(cnf_transformation,[],[f22])).
% 57.90/7.73  fof(f18839,plain,(
% 57.90/7.73    ( ! [X24,X23,X21,X22] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,X22),X23),k2_zfmisc_1(X22,X24))) )),
% 57.90/7.73    inference(forward_demodulation,[],[f18819,f92])).
% 57.90/7.73  fof(f92,plain,(
% 57.90/7.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 57.90/7.73    inference(equality_resolution,[],[f69])).
% 57.90/7.73  fof(f69,plain,(
% 57.90/7.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 57.90/7.73    inference(cnf_transformation,[],[f36])).
% 57.90/7.73  fof(f36,plain,(
% 57.90/7.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 57.90/7.73    inference(flattening,[],[f35])).
% 57.90/7.73  fof(f35,plain,(
% 57.90/7.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 57.90/7.73    inference(nnf_transformation,[],[f10])).
% 57.90/7.73  fof(f10,axiom,(
% 57.90/7.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 57.90/7.73  fof(f18819,plain,(
% 57.90/7.73    ( ! [X24,X23,X21,X22] : (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,X22),X23),k2_zfmisc_1(X22,X24)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X23,X24))) )),
% 57.90/7.73    inference(superposition,[],[f87,f2695])).
% 57.90/7.73  fof(f2695,plain,(
% 57.90/7.73    ( ! [X23,X22] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X22,X23),X23)) )),
% 57.90/7.73    inference(resolution,[],[f2680,f795])).
% 57.90/7.73  fof(f795,plain,(
% 57.90/7.73    ( ! [X16] : (r2_hidden(sK6(k1_xboole_0,X16),X16) | k1_xboole_0 = X16) )),
% 57.90/7.73    inference(resolution,[],[f150,f136])).
% 57.90/7.73  fof(f136,plain,(
% 57.90/7.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 57.90/7.73    inference(resolution,[],[f134,f105])).
% 57.90/7.73  fof(f105,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0),X0)) )),
% 57.90/7.73    inference(resolution,[],[f66,f73])).
% 57.90/7.73  fof(f73,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK7(X1),X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f40])).
% 57.90/7.73  fof(f40,plain,(
% 57.90/7.73    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)) | ~r2_hidden(X0,X1))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f39])).
% 57.90/7.73  fof(f39,plain,(
% 57.90/7.73    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f20,plain,(
% 57.90/7.73    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 57.90/7.73    inference(ennf_transformation,[],[f12])).
% 57.90/7.73  fof(f12,axiom,(
% 57.90/7.73    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 57.90/7.73  fof(f150,plain,(
% 57.90/7.73    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | r2_hidden(sK6(X1,X2),X2)) )),
% 57.90/7.73    inference(resolution,[],[f64,f71])).
% 57.90/7.73  fof(f71,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f38])).
% 57.90/7.73  fof(f38,plain,(
% 57.90/7.73    ! [X0,X1] : ((~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f37])).
% 57.90/7.73  fof(f37,plain,(
% 57.90/7.73    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f19,plain,(
% 57.90/7.73    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 57.90/7.73    inference(ennf_transformation,[],[f6])).
% 57.90/7.73  fof(f6,axiom,(
% 57.90/7.73    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 57.90/7.73  fof(f64,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f30])).
% 57.90/7.73  fof(f30,plain,(
% 57.90/7.73    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 57.90/7.73    inference(flattening,[],[f29])).
% 57.90/7.73  fof(f29,plain,(
% 57.90/7.73    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 57.90/7.73    inference(nnf_transformation,[],[f5])).
% 57.90/7.73  fof(f5,axiom,(
% 57.90/7.73    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 57.90/7.73  fof(f2680,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k4_xboole_0(X1,X2),X2))) )),
% 57.90/7.73    inference(resolution,[],[f2679,f56])).
% 57.90/7.73  fof(f2679,plain,(
% 57.90/7.73    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f2669])).
% 57.90/7.73  fof(f2669,plain,(
% 57.90/7.73    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 57.90/7.73    inference(resolution,[],[f245,f126])).
% 57.90/7.73  fof(f126,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 57.90/7.73    inference(resolution,[],[f98,f57])).
% 57.90/7.73  fof(f98,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 57.90/7.73    inference(equality_resolution,[],[f81])).
% 57.90/7.73  fof(f81,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f50])).
% 57.90/7.73  fof(f50,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 57.90/7.73  fof(f49,plain,(
% 57.90/7.73    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 57.90/7.73    introduced(choice_axiom,[])).
% 57.90/7.73  fof(f48,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(rectify,[],[f47])).
% 57.90/7.73  fof(f47,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(flattening,[],[f46])).
% 57.90/7.73  fof(f46,plain,(
% 57.90/7.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 57.90/7.73    inference(nnf_transformation,[],[f3])).
% 57.90/7.73  fof(f3,axiom,(
% 57.90/7.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 57.90/7.73  fof(f245,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 57.90/7.73    inference(resolution,[],[f121,f94])).
% 57.90/7.73  fof(f121,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 57.90/7.73    inference(resolution,[],[f97,f57])).
% 57.90/7.73  fof(f97,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 57.90/7.73    inference(equality_resolution,[],[f82])).
% 57.90/7.73  fof(f82,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f50])).
% 57.90/7.73  fof(f87,plain,(
% 57.90/7.73    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 57.90/7.73    inference(cnf_transformation,[],[f11])).
% 57.90/7.73  fof(f11,axiom,(
% 57.90/7.73    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 57.90/7.73  fof(f18823,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 57.90/7.73    inference(superposition,[],[f87,f104])).
% 57.90/7.73  fof(f104,plain,(
% 57.90/7.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 57.90/7.73    inference(resolution,[],[f58,f88])).
% 57.90/7.73  fof(f88,plain,(
% 57.90/7.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 57.90/7.73    inference(equality_resolution,[],[f60])).
% 57.90/7.73  fof(f60,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 57.90/7.73    inference(cnf_transformation,[],[f28])).
% 57.90/7.73  fof(f28,plain,(
% 57.90/7.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 57.90/7.73    inference(flattening,[],[f27])).
% 57.90/7.73  fof(f27,plain,(
% 57.90/7.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 57.90/7.73    inference(nnf_transformation,[],[f7])).
% 57.90/7.73  fof(f7,axiom,(
% 57.90/7.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 57.90/7.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 57.90/7.73  fof(f68,plain,(
% 57.90/7.73    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 57.90/7.73    inference(cnf_transformation,[],[f36])).
% 57.90/7.73  fof(f93,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 57.90/7.73    inference(equality_resolution,[],[f77])).
% 57.90/7.73  fof(f77,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f45])).
% 57.90/7.73  fof(f85107,plain,(
% 57.90/7.73    ~r1_tarski(sK0,sK2)),
% 57.90/7.73    inference(subsumption_resolution,[],[f85106,f73517])).
% 57.90/7.73  fof(f73517,plain,(
% 57.90/7.73    sK0 != sK2),
% 57.90/7.73    inference(trivial_inequality_removal,[],[f73234])).
% 57.90/7.73  fof(f73234,plain,(
% 57.90/7.73    sK1 != sK1 | sK0 != sK2),
% 57.90/7.73    inference(superposition,[],[f54,f73232])).
% 57.90/7.73  fof(f73232,plain,(
% 57.90/7.73    sK1 = sK3),
% 57.90/7.73    inference(subsumption_resolution,[],[f73231,f26329])).
% 57.90/7.73  fof(f26329,plain,(
% 57.90/7.73    r1_tarski(sK1,sK3)),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f26322])).
% 57.90/7.73  fof(f26322,plain,(
% 57.90/7.73    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)),
% 57.90/7.73    inference(resolution,[],[f26006,f66])).
% 57.90/7.73  fof(f26006,plain,(
% 57.90/7.73    ( ! [X20] : (~r2_hidden(sK5(X20,sK3),sK1) | r1_tarski(X20,sK3)) )),
% 57.90/7.73    inference(resolution,[],[f25940,f67])).
% 57.90/7.73  fof(f25940,plain,(
% 57.90/7.73    ( ! [X2] : (r2_hidden(X2,sK3) | ~r2_hidden(X2,sK1)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f25804,f134])).
% 57.90/7.73  fof(f25804,plain,(
% 57.90/7.73    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK3) | ~r2_hidden(X2,sK1)) )),
% 57.90/7.73    inference(superposition,[],[f93,f25791])).
% 57.90/7.73  fof(f25791,plain,(
% 57.90/7.73    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 57.90/7.73    inference(subsumption_resolution,[],[f25790,f52])).
% 57.90/7.73  fof(f52,plain,(
% 57.90/7.73    k1_xboole_0 != sK0),
% 57.90/7.73    inference(cnf_transformation,[],[f22])).
% 57.90/7.73  fof(f25790,plain,(
% 57.90/7.73    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 57.90/7.73    inference(trivial_inequality_removal,[],[f25774])).
% 57.90/7.73  fof(f25774,plain,(
% 57.90/7.73    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 57.90/7.73    inference(superposition,[],[f68,f25744])).
% 57.90/7.73  fof(f25744,plain,(
% 57.90/7.73    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 57.90/7.73    inference(superposition,[],[f24029,f2008])).
% 57.90/7.73  fof(f24029,plain,(
% 57.90/7.73    ( ! [X12] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X12,sK3),sK1))) )),
% 57.90/7.73    inference(superposition,[],[f18813,f21267])).
% 57.90/7.73  fof(f21267,plain,(
% 57.90/7.73    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 57.90/7.73    inference(superposition,[],[f18849,f51])).
% 57.90/7.73  fof(f18849,plain,(
% 57.90/7.73    ( ! [X24,X23,X21,X22] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,k4_xboole_0(X21,X22)),k2_zfmisc_1(X24,X22))) )),
% 57.90/7.73    inference(forward_demodulation,[],[f18829,f91])).
% 57.90/7.73  fof(f91,plain,(
% 57.90/7.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 57.90/7.73    inference(equality_resolution,[],[f70])).
% 57.90/7.73  fof(f70,plain,(
% 57.90/7.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 57.90/7.73    inference(cnf_transformation,[],[f36])).
% 57.90/7.73  fof(f18829,plain,(
% 57.90/7.73    ( ! [X24,X23,X21,X22] : (k3_xboole_0(k2_zfmisc_1(X23,k4_xboole_0(X21,X22)),k2_zfmisc_1(X24,X22)) = k2_zfmisc_1(k3_xboole_0(X23,X24),k1_xboole_0)) )),
% 57.90/7.73    inference(superposition,[],[f87,f2695])).
% 57.90/7.73  fof(f18813,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 57.90/7.73    inference(superposition,[],[f87,f104])).
% 57.90/7.73  fof(f73231,plain,(
% 57.90/7.73    sK1 = sK3 | ~r1_tarski(sK1,sK3)),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f73230])).
% 57.90/7.73  fof(f73230,plain,(
% 57.90/7.73    sK1 = sK3 | sK1 = sK3 | ~r1_tarski(sK1,sK3)),
% 57.90/7.73    inference(resolution,[],[f73215,f64])).
% 57.90/7.73  fof(f73215,plain,(
% 57.90/7.73    ~r2_xboole_0(sK1,sK3) | sK1 = sK3),
% 57.90/7.73    inference(resolution,[],[f72813,f72])).
% 57.90/7.73  fof(f72,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 57.90/7.73    inference(cnf_transformation,[],[f38])).
% 57.90/7.73  fof(f72813,plain,(
% 57.90/7.73    r2_hidden(sK6(sK1,sK3),sK1) | sK1 = sK3),
% 57.90/7.73    inference(resolution,[],[f72796,f26330])).
% 57.90/7.73  fof(f26330,plain,(
% 57.90/7.73    r2_hidden(sK6(sK1,sK3),sK3) | sK1 = sK3),
% 57.90/7.73    inference(resolution,[],[f26329,f150])).
% 57.90/7.73  fof(f72796,plain,(
% 57.90/7.73    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK1)) )),
% 57.90/7.73    inference(condensation,[],[f72606])).
% 57.90/7.73  fof(f72606,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK1) | ~r2_hidden(X0,X1)) )),
% 57.90/7.73    inference(resolution,[],[f72329,f93])).
% 57.90/7.73  fof(f72329,plain,(
% 57.90/7.73    ( ! [X92,X91] : (~r2_hidden(X92,k4_xboole_0(X91,sK1)) | ~r2_hidden(X92,sK3)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f72148,f134])).
% 57.90/7.73  fof(f72148,plain,(
% 57.90/7.73    ( ! [X92,X91] : (r2_hidden(X92,k1_xboole_0) | ~r2_hidden(X92,k4_xboole_0(X91,sK1)) | ~r2_hidden(X92,sK3)) )),
% 57.90/7.73    inference(superposition,[],[f96,f71819])).
% 57.90/7.73  fof(f71819,plain,(
% 57.90/7.73    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X1,sK1))) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f71809,f91])).
% 57.90/7.73  fof(f71809,plain,(
% 57.90/7.73    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X1,sK1))) )),
% 57.90/7.73    inference(superposition,[],[f48821,f3222])).
% 57.90/7.73  fof(f3222,plain,(
% 57.90/7.73    ( ! [X23,X22] : (k1_xboole_0 = k3_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 57.90/7.73    inference(resolution,[],[f3209,f795])).
% 57.90/7.73  fof(f3209,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 57.90/7.73    inference(resolution,[],[f3206,f56])).
% 57.90/7.73  fof(f3206,plain,(
% 57.90/7.73    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f3194])).
% 57.90/7.73  fof(f3194,plain,(
% 57.90/7.73    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 57.90/7.73    inference(resolution,[],[f354,f121])).
% 57.90/7.73  fof(f354,plain,(
% 57.90/7.73    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 57.90/7.73    inference(resolution,[],[f126,f94])).
% 57.90/7.73  fof(f48821,plain,(
% 57.90/7.73    ( ! [X26] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X26)) | k1_xboole_0 = k3_xboole_0(sK3,X26)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f48797,f52])).
% 57.90/7.73  fof(f48797,plain,(
% 57.90/7.73    ( ! [X26] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X26)) | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK3,X26)) )),
% 57.90/7.73    inference(superposition,[],[f68,f41894])).
% 57.90/7.73  fof(f41894,plain,(
% 57.90/7.73    ( ! [X5] : (k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5))) )),
% 57.90/7.73    inference(forward_demodulation,[],[f41872,f18813])).
% 57.90/7.73  fof(f41872,plain,(
% 57.90/7.73    ( ! [X5] : (k2_zfmisc_1(sK0,k3_xboole_0(sK3,X5)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X5))) )),
% 57.90/7.73    inference(superposition,[],[f18813,f41836])).
% 57.90/7.73  fof(f41836,plain,(
% 57.90/7.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 57.90/7.73    inference(subsumption_resolution,[],[f41834,f26515])).
% 57.90/7.73  fof(f26515,plain,(
% 57.90/7.73    ( ! [X249] : (r1_tarski(k2_zfmisc_1(X249,sK1),k2_zfmisc_1(X249,sK3))) )),
% 57.90/7.73    inference(superposition,[],[f24133,f26334])).
% 57.90/7.73  fof(f26334,plain,(
% 57.90/7.73    sK1 = k3_xboole_0(sK1,sK3)),
% 57.90/7.73    inference(resolution,[],[f26329,f58])).
% 57.90/7.73  fof(f24133,plain,(
% 57.90/7.73    ( ! [X432,X434,X433] : (r1_tarski(k2_zfmisc_1(X432,k3_xboole_0(X433,X434)),k2_zfmisc_1(X432,X434))) )),
% 57.90/7.73    inference(superposition,[],[f2143,f18813])).
% 57.90/7.73  fof(f2143,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 57.90/7.73    inference(duplicate_literal_removal,[],[f2117])).
% 57.90/7.73  fof(f2117,plain,(
% 57.90/7.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 57.90/7.73    inference(resolution,[],[f124,f67])).
% 57.90/7.73  fof(f124,plain,(
% 57.90/7.73    ( ! [X8,X7,X9] : (r2_hidden(sK5(k3_xboole_0(X7,X8),X9),X8) | r1_tarski(k3_xboole_0(X7,X8),X9)) )),
% 57.90/7.73    inference(resolution,[],[f97,f66])).
% 57.90/7.73  fof(f41834,plain,(
% 57.90/7.73    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 57.90/7.73    inference(resolution,[],[f41657,f61])).
% 57.90/7.73  fof(f61,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 57.90/7.73    inference(cnf_transformation,[],[f28])).
% 57.90/7.73  fof(f41657,plain,(
% 57.90/7.73    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 57.90/7.73    inference(superposition,[],[f40017,f41622])).
% 57.90/7.73  fof(f41622,plain,(
% 57.90/7.73    sK0 = k3_xboole_0(sK0,sK2)),
% 57.90/7.73    inference(resolution,[],[f41617,f58])).
% 57.90/7.73  fof(f40017,plain,(
% 57.90/7.73    ( ! [X18] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X18,sK2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 57.90/7.73    inference(superposition,[],[f39109,f51])).
% 57.90/7.73  fof(f39109,plain,(
% 57.90/7.73    ( ! [X441,X440,X442] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X440,X442),X441),k2_zfmisc_1(X442,X441))) )),
% 57.90/7.73    inference(superposition,[],[f2143,f18823])).
% 57.90/7.73  fof(f96,plain,(
% 57.90/7.73    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 57.90/7.73    inference(equality_resolution,[],[f83])).
% 57.90/7.73  fof(f83,plain,(
% 57.90/7.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 57.90/7.73    inference(cnf_transformation,[],[f50])).
% 57.90/7.73  fof(f54,plain,(
% 57.90/7.73    sK1 != sK3 | sK0 != sK2),
% 57.90/7.73    inference(cnf_transformation,[],[f22])).
% 57.90/7.73  fof(f85106,plain,(
% 57.90/7.73    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 57.90/7.73    inference(resolution,[],[f85091,f64])).
% 57.90/7.73  fof(f85091,plain,(
% 57.90/7.73    ~r2_xboole_0(sK0,sK2)),
% 57.90/7.73    inference(resolution,[],[f84997,f72])).
% 57.90/7.73  fof(f84997,plain,(
% 57.90/7.73    r2_hidden(sK6(sK0,sK2),sK0)),
% 57.90/7.73    inference(subsumption_resolution,[],[f84725,f73517])).
% 57.90/7.73  fof(f84725,plain,(
% 57.90/7.73    r2_hidden(sK6(sK0,sK2),sK0) | sK0 = sK2),
% 57.90/7.73    inference(resolution,[],[f84696,f41618])).
% 57.90/7.73  fof(f41618,plain,(
% 57.90/7.73    r2_hidden(sK6(sK0,sK2),sK2) | sK0 = sK2),
% 57.90/7.73    inference(resolution,[],[f41617,f150])).
% 57.90/7.73  fof(f84696,plain,(
% 57.90/7.73    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 57.90/7.73    inference(condensation,[],[f84492])).
% 57.90/7.73  fof(f84492,plain,(
% 57.90/7.73    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0) | ~r2_hidden(X0,X1)) )),
% 57.90/7.73    inference(resolution,[],[f84188,f93])).
% 57.90/7.73  fof(f84188,plain,(
% 57.90/7.73    ( ! [X94,X93] : (~r2_hidden(X94,k4_xboole_0(X93,sK0)) | ~r2_hidden(X94,sK2)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f84005,f134])).
% 57.90/7.73  fof(f84005,plain,(
% 57.90/7.73    ( ! [X94,X93] : (r2_hidden(X94,k1_xboole_0) | ~r2_hidden(X94,k4_xboole_0(X93,sK0)) | ~r2_hidden(X94,sK2)) )),
% 57.90/7.73    inference(superposition,[],[f96,f83671])).
% 57.90/7.73  fof(f83671,plain,(
% 57.90/7.73    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X1,sK0))) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f83658,f92])).
% 57.90/7.73  fof(f83658,plain,(
% 57.90/7.73    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X1,sK0))) )),
% 57.90/7.73    inference(superposition,[],[f74446,f3222])).
% 57.90/7.73  fof(f74446,plain,(
% 57.90/7.73    ( ! [X45] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X45),sK1) | k1_xboole_0 = k3_xboole_0(sK2,X45)) )),
% 57.90/7.73    inference(subsumption_resolution,[],[f74404,f53])).
% 57.90/7.73  fof(f74404,plain,(
% 57.90/7.73    ( ! [X45] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X45),sK1) | k1_xboole_0 = k3_xboole_0(sK2,X45) | k1_xboole_0 = sK1) )),
% 57.90/7.73    inference(superposition,[],[f68,f73650])).
% 57.90/7.73  fof(f73650,plain,(
% 57.90/7.73    ( ! [X36] : (k2_zfmisc_1(k3_xboole_0(sK2,X36),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X36),sK1)) )),
% 57.90/7.73    inference(forward_demodulation,[],[f73622,f18823])).
% 57.90/7.73  fof(f73622,plain,(
% 57.90/7.73    ( ! [X36] : (k2_zfmisc_1(k3_xboole_0(sK2,X36),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X36,sK1))) )),
% 57.90/7.73    inference(superposition,[],[f18823,f73233])).
% 57.90/7.73  fof(f73233,plain,(
% 57.90/7.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 57.90/7.73    inference(superposition,[],[f51,f73232])).
% 57.90/7.73  % SZS output end Proof for theBenchmark
% 57.90/7.73  % (4541)------------------------------
% 57.90/7.73  % (4541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.90/7.73  % (4541)Termination reason: Refutation
% 57.90/7.73  
% 57.90/7.73  % (4541)Memory used [KB]: 240891
% 57.90/7.73  % (4541)Time elapsed: 6.803 s
% 57.90/7.73  % (4541)------------------------------
% 57.90/7.73  % (4541)------------------------------
% 57.90/7.75  % (4473)Success in time 7.384 s
%------------------------------------------------------------------------------
