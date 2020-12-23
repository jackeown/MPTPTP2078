%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:25 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 436 expanded)
%              Number of clauses        :   94 ( 164 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  435 (1540 expanded)
%              Number of equality atoms :  200 ( 484 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 != k9_relat_1(sK3,sK2) )
      & ( r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 = k9_relat_1(sK3,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 != k9_relat_1(sK3,sK2) )
    & ( r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 = k9_relat_1(sK3,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1026,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2)
    | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1044,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2040,plain,
    ( k9_relat_1(sK3,sK2) = k1_xboole_0
    | r1_xboole_0(sK2,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1044])).

cnf(c_21,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1042,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1032,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1034,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1043,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2868,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X3) != iProver_top
    | r1_xboole_0(X3,X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1043])).

cnf(c_10670,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_xboole_0(k1_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_2868])).

cnf(c_28376,plain,
    ( r1_xboole_0(X0,k9_relat_1(X1,X2)) = iProver_top
    | r1_xboole_0(k1_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_10670])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1040,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_29756,plain,
    ( k9_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28376,c_1040])).

cnf(c_32860,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_29756])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_67,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_33094,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32860,c_67])).

cnf(c_33095,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_33094])).

cnf(c_33100,plain,
    ( k9_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = k1_xboole_0
    | k9_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2040,c_33095])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2043,plain,
    ( k9_relat_1(sK3,sK2) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_1044])).

cnf(c_32828,plain,
    ( k9_relat_1(sK3,sK2) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_29756])).

cnf(c_33397,plain,
    ( k9_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33100,c_29,c_32828])).

cnf(c_1025,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1036,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_314,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X0,X2) = X0
    | k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) != X2
    | k1_relat_1(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_315,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_relat_1(X0))
    | k7_relat_1(X0,k2_zfmisc_1(k1_relat_1(k1_relat_1(X0)),k2_relat_1(k1_relat_1(X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1024,plain,
    ( k7_relat_1(X0,k2_zfmisc_1(k1_relat_1(k1_relat_1(X0)),k2_relat_1(k1_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1364,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k1_relat_1(k6_relat_1(X0))),k2_relat_1(k1_relat_1(k6_relat_1(X0))))) = k6_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1024])).

cnf(c_1365,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1364,c_21])).

cnf(c_3799,plain,
    ( v1_relat_1(X0) != iProver_top
    | k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_67])).

cnf(c_3800,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3799])).

cnf(c_3806,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(X0,X1)),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) = k6_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_3800])).

cnf(c_15849,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0)))) = k6_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1025,c_3806])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1031,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2215,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1025,c_1031])).

cnf(c_15853,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k6_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_15849,c_2215])).

cnf(c_1037,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2213,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1037,c_1031])).

cnf(c_16290,plain,
    ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k2_relat_1(k6_relat_1(k7_relat_1(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_15853,c_2213])).

cnf(c_20,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16307,plain,
    ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_16290,c_20])).

cnf(c_33410,plain,
    ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,sK2)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0)) = k7_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_33397,c_16307])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1038,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1628,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1038])).

cnf(c_2871,plain,
    ( r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1628])).

cnf(c_3164,plain,
    ( r1_xboole_0(X0,k9_relat_1(X1,k1_xboole_0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_2871])).

cnf(c_3296,plain,
    ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_1040])).

cnf(c_3301,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1037,c_3296])).

cnf(c_33435,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33410,c_6,c_3301])).

cnf(c_22542,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_31120,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_22542])).

cnf(c_534,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13895,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_13896,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13895])).

cnf(c_535,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6836,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2)))
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X1
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_6838,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6836])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1237,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5636,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_542,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2404,plain,
    ( k7_relat_1(sK3,sK2) != X0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_2405,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_1486,plain,
    ( X0 != X1
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X1
    | k1_relat_1(k7_relat_1(sK3,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1900,plain,
    ( X0 != k1_relat_1(X1)
    | k1_relat_1(k7_relat_1(sK3,sK2)) = X0
    | k1_relat_1(k7_relat_1(sK3,sK2)) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_1901,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_1093,plain,
    ( k9_relat_1(sK3,sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1094,plain,
    ( k9_relat_1(sK3,sK2) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK3,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1072,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK2),sK2)
    | r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1073,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_73,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33435,c_32828,c_31120,c_13896,c_6838,c_5636,c_2405,c_1901,c_1094,c_1072,c_1073,c_5,c_74,c_73,c_19,c_26,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.85/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.85/1.98  
% 11.85/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/1.98  
% 11.85/1.98  ------  iProver source info
% 11.85/1.98  
% 11.85/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.85/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/1.98  git: non_committed_changes: false
% 11.85/1.98  git: last_make_outside_of_git: false
% 11.85/1.98  
% 11.85/1.98  ------ 
% 11.85/1.98  
% 11.85/1.98  ------ Input Options
% 11.85/1.98  
% 11.85/1.98  --out_options                           all
% 11.85/1.98  --tptp_safe_out                         true
% 11.85/1.98  --problem_path                          ""
% 11.85/1.98  --include_path                          ""
% 11.85/1.98  --clausifier                            res/vclausify_rel
% 11.85/1.98  --clausifier_options                    ""
% 11.85/1.98  --stdin                                 false
% 11.85/1.98  --stats_out                             all
% 11.85/1.98  
% 11.85/1.98  ------ General Options
% 11.85/1.98  
% 11.85/1.98  --fof                                   false
% 11.85/1.98  --time_out_real                         305.
% 11.85/1.98  --time_out_virtual                      -1.
% 11.85/1.98  --symbol_type_check                     false
% 11.85/1.98  --clausify_out                          false
% 11.85/1.98  --sig_cnt_out                           false
% 11.85/1.98  --trig_cnt_out                          false
% 11.85/1.98  --trig_cnt_out_tolerance                1.
% 11.85/1.98  --trig_cnt_out_sk_spl                   false
% 11.85/1.98  --abstr_cl_out                          false
% 11.85/1.98  
% 11.85/1.98  ------ Global Options
% 11.85/1.98  
% 11.85/1.98  --schedule                              default
% 11.85/1.98  --add_important_lit                     false
% 11.85/1.98  --prop_solver_per_cl                    1000
% 11.85/1.98  --min_unsat_core                        false
% 11.85/1.98  --soft_assumptions                      false
% 11.85/1.98  --soft_lemma_size                       3
% 11.85/1.98  --prop_impl_unit_size                   0
% 11.85/1.98  --prop_impl_unit                        []
% 11.85/1.98  --share_sel_clauses                     true
% 11.85/1.98  --reset_solvers                         false
% 11.85/1.98  --bc_imp_inh                            [conj_cone]
% 11.85/1.98  --conj_cone_tolerance                   3.
% 11.85/1.98  --extra_neg_conj                        none
% 11.85/1.98  --large_theory_mode                     true
% 11.85/1.98  --prolific_symb_bound                   200
% 11.85/1.98  --lt_threshold                          2000
% 11.85/1.98  --clause_weak_htbl                      true
% 11.85/1.98  --gc_record_bc_elim                     false
% 11.85/1.98  
% 11.85/1.98  ------ Preprocessing Options
% 11.85/1.98  
% 11.85/1.98  --preprocessing_flag                    true
% 11.85/1.98  --time_out_prep_mult                    0.1
% 11.85/1.98  --splitting_mode                        input
% 11.85/1.98  --splitting_grd                         true
% 11.85/1.98  --splitting_cvd                         false
% 11.85/1.98  --splitting_cvd_svl                     false
% 11.85/1.98  --splitting_nvd                         32
% 11.85/1.98  --sub_typing                            true
% 11.85/1.98  --prep_gs_sim                           true
% 11.85/1.98  --prep_unflatten                        true
% 11.85/1.98  --prep_res_sim                          true
% 11.85/1.98  --prep_upred                            true
% 11.85/1.98  --prep_sem_filter                       exhaustive
% 11.85/1.98  --prep_sem_filter_out                   false
% 11.85/1.98  --pred_elim                             true
% 11.85/1.98  --res_sim_input                         true
% 11.85/1.98  --eq_ax_congr_red                       true
% 11.85/1.98  --pure_diseq_elim                       true
% 11.85/1.98  --brand_transform                       false
% 11.85/1.98  --non_eq_to_eq                          false
% 11.85/1.98  --prep_def_merge                        true
% 11.85/1.98  --prep_def_merge_prop_impl              false
% 11.85/1.98  --prep_def_merge_mbd                    true
% 11.85/1.98  --prep_def_merge_tr_red                 false
% 11.85/1.98  --prep_def_merge_tr_cl                  false
% 11.85/1.98  --smt_preprocessing                     true
% 11.85/1.98  --smt_ac_axioms                         fast
% 11.85/1.98  --preprocessed_out                      false
% 11.85/1.98  --preprocessed_stats                    false
% 11.85/1.98  
% 11.85/1.98  ------ Abstraction refinement Options
% 11.85/1.98  
% 11.85/1.98  --abstr_ref                             []
% 11.85/1.98  --abstr_ref_prep                        false
% 11.85/1.98  --abstr_ref_until_sat                   false
% 11.85/1.98  --abstr_ref_sig_restrict                funpre
% 11.85/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.98  --abstr_ref_under                       []
% 11.85/1.98  
% 11.85/1.98  ------ SAT Options
% 11.85/1.98  
% 11.85/1.98  --sat_mode                              false
% 11.85/1.98  --sat_fm_restart_options                ""
% 11.85/1.98  --sat_gr_def                            false
% 11.85/1.98  --sat_epr_types                         true
% 11.85/1.98  --sat_non_cyclic_types                  false
% 11.85/1.98  --sat_finite_models                     false
% 11.85/1.98  --sat_fm_lemmas                         false
% 11.85/1.98  --sat_fm_prep                           false
% 11.85/1.98  --sat_fm_uc_incr                        true
% 11.85/1.98  --sat_out_model                         small
% 11.85/1.98  --sat_out_clauses                       false
% 11.85/1.98  
% 11.85/1.98  ------ QBF Options
% 11.85/1.98  
% 11.85/1.98  --qbf_mode                              false
% 11.85/1.98  --qbf_elim_univ                         false
% 11.85/1.98  --qbf_dom_inst                          none
% 11.85/1.98  --qbf_dom_pre_inst                      false
% 11.85/1.98  --qbf_sk_in                             false
% 11.85/1.98  --qbf_pred_elim                         true
% 11.85/1.98  --qbf_split                             512
% 11.85/1.98  
% 11.85/1.98  ------ BMC1 Options
% 11.85/1.98  
% 11.85/1.98  --bmc1_incremental                      false
% 11.85/1.98  --bmc1_axioms                           reachable_all
% 11.85/1.98  --bmc1_min_bound                        0
% 11.85/1.98  --bmc1_max_bound                        -1
% 11.85/1.98  --bmc1_max_bound_default                -1
% 11.85/1.98  --bmc1_symbol_reachability              true
% 11.85/1.98  --bmc1_property_lemmas                  false
% 11.85/1.98  --bmc1_k_induction                      false
% 11.85/1.98  --bmc1_non_equiv_states                 false
% 11.85/1.98  --bmc1_deadlock                         false
% 11.85/1.98  --bmc1_ucm                              false
% 11.85/1.98  --bmc1_add_unsat_core                   none
% 11.85/1.98  --bmc1_unsat_core_children              false
% 11.85/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.98  --bmc1_out_stat                         full
% 11.85/1.98  --bmc1_ground_init                      false
% 11.85/1.98  --bmc1_pre_inst_next_state              false
% 11.85/1.98  --bmc1_pre_inst_state                   false
% 11.85/1.98  --bmc1_pre_inst_reach_state             false
% 11.85/1.98  --bmc1_out_unsat_core                   false
% 11.85/1.98  --bmc1_aig_witness_out                  false
% 11.85/1.98  --bmc1_verbose                          false
% 11.85/1.98  --bmc1_dump_clauses_tptp                false
% 11.85/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.98  --bmc1_dump_file                        -
% 11.85/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.98  --bmc1_ucm_extend_mode                  1
% 11.85/1.98  --bmc1_ucm_init_mode                    2
% 11.85/1.98  --bmc1_ucm_cone_mode                    none
% 11.85/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.98  --bmc1_ucm_relax_model                  4
% 11.85/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.98  --bmc1_ucm_layered_model                none
% 11.85/1.98  --bmc1_ucm_max_lemma_size               10
% 11.85/1.98  
% 11.85/1.98  ------ AIG Options
% 11.85/1.98  
% 11.85/1.98  --aig_mode                              false
% 11.85/1.98  
% 11.85/1.98  ------ Instantiation Options
% 11.85/1.98  
% 11.85/1.98  --instantiation_flag                    true
% 11.85/1.98  --inst_sos_flag                         true
% 11.85/1.98  --inst_sos_phase                        true
% 11.85/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.98  --inst_lit_sel_side                     num_symb
% 11.85/1.98  --inst_solver_per_active                1400
% 11.85/1.98  --inst_solver_calls_frac                1.
% 11.85/1.98  --inst_passive_queue_type               priority_queues
% 11.85/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.98  --inst_passive_queues_freq              [25;2]
% 11.85/1.98  --inst_dismatching                      true
% 11.85/1.98  --inst_eager_unprocessed_to_passive     true
% 11.85/1.98  --inst_prop_sim_given                   true
% 11.85/1.98  --inst_prop_sim_new                     false
% 11.85/1.98  --inst_subs_new                         false
% 11.85/1.98  --inst_eq_res_simp                      false
% 11.85/1.98  --inst_subs_given                       false
% 11.85/1.98  --inst_orphan_elimination               true
% 11.85/1.98  --inst_learning_loop_flag               true
% 11.85/1.98  --inst_learning_start                   3000
% 11.85/1.98  --inst_learning_factor                  2
% 11.85/1.98  --inst_start_prop_sim_after_learn       3
% 11.85/1.98  --inst_sel_renew                        solver
% 11.85/1.98  --inst_lit_activity_flag                true
% 11.85/1.98  --inst_restr_to_given                   false
% 11.85/1.98  --inst_activity_threshold               500
% 11.85/1.98  --inst_out_proof                        true
% 11.85/1.98  
% 11.85/1.98  ------ Resolution Options
% 11.85/1.98  
% 11.85/1.98  --resolution_flag                       true
% 11.85/1.98  --res_lit_sel                           adaptive
% 11.85/1.98  --res_lit_sel_side                      none
% 11.85/1.98  --res_ordering                          kbo
% 11.85/1.98  --res_to_prop_solver                    active
% 11.85/1.98  --res_prop_simpl_new                    false
% 11.85/1.98  --res_prop_simpl_given                  true
% 11.85/1.98  --res_passive_queue_type                priority_queues
% 11.85/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.98  --res_passive_queues_freq               [15;5]
% 11.85/1.98  --res_forward_subs                      full
% 11.85/1.98  --res_backward_subs                     full
% 11.85/1.98  --res_forward_subs_resolution           true
% 11.85/1.98  --res_backward_subs_resolution          true
% 11.85/1.98  --res_orphan_elimination                true
% 11.85/1.98  --res_time_limit                        2.
% 11.85/1.98  --res_out_proof                         true
% 11.85/1.98  
% 11.85/1.98  ------ Superposition Options
% 11.85/1.98  
% 11.85/1.98  --superposition_flag                    true
% 11.85/1.98  --sup_passive_queue_type                priority_queues
% 11.85/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.98  --demod_completeness_check              fast
% 11.85/1.98  --demod_use_ground                      true
% 11.85/1.98  --sup_to_prop_solver                    passive
% 11.85/1.98  --sup_prop_simpl_new                    true
% 11.85/1.98  --sup_prop_simpl_given                  true
% 11.85/1.98  --sup_fun_splitting                     true
% 11.85/1.98  --sup_smt_interval                      50000
% 11.85/1.98  
% 11.85/1.98  ------ Superposition Simplification Setup
% 11.85/1.98  
% 11.85/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.98  --sup_immed_triv                        [TrivRules]
% 11.85/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_immed_bw_main                     []
% 11.85/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_input_bw                          []
% 11.85/1.98  
% 11.85/1.98  ------ Combination Options
% 11.85/1.98  
% 11.85/1.98  --comb_res_mult                         3
% 11.85/1.98  --comb_sup_mult                         2
% 11.85/1.98  --comb_inst_mult                        10
% 11.85/1.98  
% 11.85/1.98  ------ Debug Options
% 11.85/1.98  
% 11.85/1.98  --dbg_backtrace                         false
% 11.85/1.98  --dbg_dump_prop_clauses                 false
% 11.85/1.98  --dbg_dump_prop_clauses_file            -
% 11.85/1.98  --dbg_out_stat                          false
% 11.85/1.98  ------ Parsing...
% 11.85/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/1.98  
% 11.85/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.85/1.98  
% 11.85/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/1.98  
% 11.85/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/1.98  ------ Proving...
% 11.85/1.98  ------ Problem Properties 
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  clauses                                 28
% 11.85/1.98  conjectures                             3
% 11.85/1.98  EPR                                     5
% 11.85/1.98  Horn                                    24
% 11.85/1.98  unary                                   10
% 11.85/1.98  binary                                  8
% 11.85/1.98  lits                                    59
% 11.85/1.98  lits eq                                 14
% 11.85/1.98  fd_pure                                 0
% 11.85/1.98  fd_pseudo                               0
% 11.85/1.98  fd_cond                                 2
% 11.85/1.98  fd_pseudo_cond                          0
% 11.85/1.98  AC symbols                              0
% 11.85/1.98  
% 11.85/1.98  ------ Schedule dynamic 5 is on 
% 11.85/1.98  
% 11.85/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  ------ 
% 11.85/1.98  Current options:
% 11.85/1.98  ------ 
% 11.85/1.98  
% 11.85/1.98  ------ Input Options
% 11.85/1.98  
% 11.85/1.98  --out_options                           all
% 11.85/1.98  --tptp_safe_out                         true
% 11.85/1.98  --problem_path                          ""
% 11.85/1.98  --include_path                          ""
% 11.85/1.98  --clausifier                            res/vclausify_rel
% 11.85/1.98  --clausifier_options                    ""
% 11.85/1.98  --stdin                                 false
% 11.85/1.98  --stats_out                             all
% 11.85/1.98  
% 11.85/1.98  ------ General Options
% 11.85/1.98  
% 11.85/1.98  --fof                                   false
% 11.85/1.98  --time_out_real                         305.
% 11.85/1.98  --time_out_virtual                      -1.
% 11.85/1.98  --symbol_type_check                     false
% 11.85/1.98  --clausify_out                          false
% 11.85/1.98  --sig_cnt_out                           false
% 11.85/1.98  --trig_cnt_out                          false
% 11.85/1.98  --trig_cnt_out_tolerance                1.
% 11.85/1.98  --trig_cnt_out_sk_spl                   false
% 11.85/1.98  --abstr_cl_out                          false
% 11.85/1.98  
% 11.85/1.98  ------ Global Options
% 11.85/1.98  
% 11.85/1.98  --schedule                              default
% 11.85/1.98  --add_important_lit                     false
% 11.85/1.98  --prop_solver_per_cl                    1000
% 11.85/1.98  --min_unsat_core                        false
% 11.85/1.98  --soft_assumptions                      false
% 11.85/1.98  --soft_lemma_size                       3
% 11.85/1.98  --prop_impl_unit_size                   0
% 11.85/1.98  --prop_impl_unit                        []
% 11.85/1.98  --share_sel_clauses                     true
% 11.85/1.98  --reset_solvers                         false
% 11.85/1.98  --bc_imp_inh                            [conj_cone]
% 11.85/1.98  --conj_cone_tolerance                   3.
% 11.85/1.98  --extra_neg_conj                        none
% 11.85/1.98  --large_theory_mode                     true
% 11.85/1.98  --prolific_symb_bound                   200
% 11.85/1.98  --lt_threshold                          2000
% 11.85/1.98  --clause_weak_htbl                      true
% 11.85/1.98  --gc_record_bc_elim                     false
% 11.85/1.98  
% 11.85/1.98  ------ Preprocessing Options
% 11.85/1.98  
% 11.85/1.98  --preprocessing_flag                    true
% 11.85/1.98  --time_out_prep_mult                    0.1
% 11.85/1.98  --splitting_mode                        input
% 11.85/1.98  --splitting_grd                         true
% 11.85/1.98  --splitting_cvd                         false
% 11.85/1.98  --splitting_cvd_svl                     false
% 11.85/1.98  --splitting_nvd                         32
% 11.85/1.98  --sub_typing                            true
% 11.85/1.98  --prep_gs_sim                           true
% 11.85/1.98  --prep_unflatten                        true
% 11.85/1.98  --prep_res_sim                          true
% 11.85/1.98  --prep_upred                            true
% 11.85/1.98  --prep_sem_filter                       exhaustive
% 11.85/1.98  --prep_sem_filter_out                   false
% 11.85/1.98  --pred_elim                             true
% 11.85/1.98  --res_sim_input                         true
% 11.85/1.98  --eq_ax_congr_red                       true
% 11.85/1.98  --pure_diseq_elim                       true
% 11.85/1.98  --brand_transform                       false
% 11.85/1.98  --non_eq_to_eq                          false
% 11.85/1.98  --prep_def_merge                        true
% 11.85/1.98  --prep_def_merge_prop_impl              false
% 11.85/1.98  --prep_def_merge_mbd                    true
% 11.85/1.98  --prep_def_merge_tr_red                 false
% 11.85/1.98  --prep_def_merge_tr_cl                  false
% 11.85/1.98  --smt_preprocessing                     true
% 11.85/1.98  --smt_ac_axioms                         fast
% 11.85/1.98  --preprocessed_out                      false
% 11.85/1.98  --preprocessed_stats                    false
% 11.85/1.98  
% 11.85/1.98  ------ Abstraction refinement Options
% 11.85/1.98  
% 11.85/1.98  --abstr_ref                             []
% 11.85/1.98  --abstr_ref_prep                        false
% 11.85/1.98  --abstr_ref_until_sat                   false
% 11.85/1.98  --abstr_ref_sig_restrict                funpre
% 11.85/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.98  --abstr_ref_under                       []
% 11.85/1.98  
% 11.85/1.98  ------ SAT Options
% 11.85/1.98  
% 11.85/1.98  --sat_mode                              false
% 11.85/1.98  --sat_fm_restart_options                ""
% 11.85/1.98  --sat_gr_def                            false
% 11.85/1.98  --sat_epr_types                         true
% 11.85/1.98  --sat_non_cyclic_types                  false
% 11.85/1.98  --sat_finite_models                     false
% 11.85/1.98  --sat_fm_lemmas                         false
% 11.85/1.98  --sat_fm_prep                           false
% 11.85/1.98  --sat_fm_uc_incr                        true
% 11.85/1.98  --sat_out_model                         small
% 11.85/1.98  --sat_out_clauses                       false
% 11.85/1.98  
% 11.85/1.98  ------ QBF Options
% 11.85/1.98  
% 11.85/1.98  --qbf_mode                              false
% 11.85/1.98  --qbf_elim_univ                         false
% 11.85/1.98  --qbf_dom_inst                          none
% 11.85/1.98  --qbf_dom_pre_inst                      false
% 11.85/1.98  --qbf_sk_in                             false
% 11.85/1.98  --qbf_pred_elim                         true
% 11.85/1.98  --qbf_split                             512
% 11.85/1.98  
% 11.85/1.98  ------ BMC1 Options
% 11.85/1.98  
% 11.85/1.98  --bmc1_incremental                      false
% 11.85/1.98  --bmc1_axioms                           reachable_all
% 11.85/1.98  --bmc1_min_bound                        0
% 11.85/1.98  --bmc1_max_bound                        -1
% 11.85/1.98  --bmc1_max_bound_default                -1
% 11.85/1.98  --bmc1_symbol_reachability              true
% 11.85/1.98  --bmc1_property_lemmas                  false
% 11.85/1.98  --bmc1_k_induction                      false
% 11.85/1.98  --bmc1_non_equiv_states                 false
% 11.85/1.98  --bmc1_deadlock                         false
% 11.85/1.98  --bmc1_ucm                              false
% 11.85/1.98  --bmc1_add_unsat_core                   none
% 11.85/1.98  --bmc1_unsat_core_children              false
% 11.85/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.98  --bmc1_out_stat                         full
% 11.85/1.98  --bmc1_ground_init                      false
% 11.85/1.98  --bmc1_pre_inst_next_state              false
% 11.85/1.98  --bmc1_pre_inst_state                   false
% 11.85/1.98  --bmc1_pre_inst_reach_state             false
% 11.85/1.98  --bmc1_out_unsat_core                   false
% 11.85/1.98  --bmc1_aig_witness_out                  false
% 11.85/1.98  --bmc1_verbose                          false
% 11.85/1.98  --bmc1_dump_clauses_tptp                false
% 11.85/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.98  --bmc1_dump_file                        -
% 11.85/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.98  --bmc1_ucm_extend_mode                  1
% 11.85/1.98  --bmc1_ucm_init_mode                    2
% 11.85/1.98  --bmc1_ucm_cone_mode                    none
% 11.85/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.98  --bmc1_ucm_relax_model                  4
% 11.85/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.98  --bmc1_ucm_layered_model                none
% 11.85/1.98  --bmc1_ucm_max_lemma_size               10
% 11.85/1.98  
% 11.85/1.98  ------ AIG Options
% 11.85/1.98  
% 11.85/1.98  --aig_mode                              false
% 11.85/1.98  
% 11.85/1.98  ------ Instantiation Options
% 11.85/1.98  
% 11.85/1.98  --instantiation_flag                    true
% 11.85/1.98  --inst_sos_flag                         true
% 11.85/1.98  --inst_sos_phase                        true
% 11.85/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.98  --inst_lit_sel_side                     none
% 11.85/1.98  --inst_solver_per_active                1400
% 11.85/1.98  --inst_solver_calls_frac                1.
% 11.85/1.98  --inst_passive_queue_type               priority_queues
% 11.85/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.98  --inst_passive_queues_freq              [25;2]
% 11.85/1.98  --inst_dismatching                      true
% 11.85/1.98  --inst_eager_unprocessed_to_passive     true
% 11.85/1.98  --inst_prop_sim_given                   true
% 11.85/1.98  --inst_prop_sim_new                     false
% 11.85/1.98  --inst_subs_new                         false
% 11.85/1.98  --inst_eq_res_simp                      false
% 11.85/1.98  --inst_subs_given                       false
% 11.85/1.98  --inst_orphan_elimination               true
% 11.85/1.98  --inst_learning_loop_flag               true
% 11.85/1.98  --inst_learning_start                   3000
% 11.85/1.98  --inst_learning_factor                  2
% 11.85/1.98  --inst_start_prop_sim_after_learn       3
% 11.85/1.98  --inst_sel_renew                        solver
% 11.85/1.98  --inst_lit_activity_flag                true
% 11.85/1.98  --inst_restr_to_given                   false
% 11.85/1.98  --inst_activity_threshold               500
% 11.85/1.98  --inst_out_proof                        true
% 11.85/1.98  
% 11.85/1.98  ------ Resolution Options
% 11.85/1.98  
% 11.85/1.98  --resolution_flag                       false
% 11.85/1.98  --res_lit_sel                           adaptive
% 11.85/1.98  --res_lit_sel_side                      none
% 11.85/1.98  --res_ordering                          kbo
% 11.85/1.98  --res_to_prop_solver                    active
% 11.85/1.98  --res_prop_simpl_new                    false
% 11.85/1.98  --res_prop_simpl_given                  true
% 11.85/1.98  --res_passive_queue_type                priority_queues
% 11.85/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.98  --res_passive_queues_freq               [15;5]
% 11.85/1.98  --res_forward_subs                      full
% 11.85/1.98  --res_backward_subs                     full
% 11.85/1.98  --res_forward_subs_resolution           true
% 11.85/1.98  --res_backward_subs_resolution          true
% 11.85/1.98  --res_orphan_elimination                true
% 11.85/1.98  --res_time_limit                        2.
% 11.85/1.98  --res_out_proof                         true
% 11.85/1.98  
% 11.85/1.98  ------ Superposition Options
% 11.85/1.98  
% 11.85/1.98  --superposition_flag                    true
% 11.85/1.98  --sup_passive_queue_type                priority_queues
% 11.85/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.98  --demod_completeness_check              fast
% 11.85/1.98  --demod_use_ground                      true
% 11.85/1.98  --sup_to_prop_solver                    passive
% 11.85/1.98  --sup_prop_simpl_new                    true
% 11.85/1.98  --sup_prop_simpl_given                  true
% 11.85/1.98  --sup_fun_splitting                     true
% 11.85/1.98  --sup_smt_interval                      50000
% 11.85/1.98  
% 11.85/1.98  ------ Superposition Simplification Setup
% 11.85/1.98  
% 11.85/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.98  --sup_immed_triv                        [TrivRules]
% 11.85/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_immed_bw_main                     []
% 11.85/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.98  --sup_input_bw                          []
% 11.85/1.98  
% 11.85/1.98  ------ Combination Options
% 11.85/1.98  
% 11.85/1.98  --comb_res_mult                         3
% 11.85/1.98  --comb_sup_mult                         2
% 11.85/1.98  --comb_inst_mult                        10
% 11.85/1.98  
% 11.85/1.98  ------ Debug Options
% 11.85/1.98  
% 11.85/1.98  --dbg_backtrace                         false
% 11.85/1.98  --dbg_dump_prop_clauses                 false
% 11.85/1.98  --dbg_dump_prop_clauses_file            -
% 11.85/1.98  --dbg_out_stat                          false
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  ------ Proving...
% 11.85/1.98  
% 11.85/1.98  
% 11.85/1.98  % SZS status Theorem for theBenchmark.p
% 11.85/1.98  
% 11.85/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/1.98  
% 11.85/1.98  fof(f15,conjecture,(
% 11.85/1.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f16,negated_conjecture,(
% 11.85/1.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.85/1.98    inference(negated_conjecture,[],[f15])).
% 11.85/1.98  
% 11.85/1.98  fof(f28,plain,(
% 11.85/1.98    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 11.85/1.98    inference(ennf_transformation,[],[f16])).
% 11.85/1.98  
% 11.85/1.98  fof(f39,plain,(
% 11.85/1.98    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 11.85/1.98    inference(nnf_transformation,[],[f28])).
% 11.85/1.98  
% 11.85/1.98  fof(f40,plain,(
% 11.85/1.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 11.85/1.98    inference(flattening,[],[f39])).
% 11.85/1.98  
% 11.85/1.98  fof(f41,plain,(
% 11.85/1.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k9_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k9_relat_1(sK3,sK2)) & v1_relat_1(sK3))),
% 11.85/1.98    introduced(choice_axiom,[])).
% 11.85/1.98  
% 11.85/1.98  fof(f42,plain,(
% 11.85/1.98    (~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k9_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k9_relat_1(sK3,sK2)) & v1_relat_1(sK3)),
% 11.85/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).
% 11.85/1.98  
% 11.85/1.98  fof(f70,plain,(
% 11.85/1.98    r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k9_relat_1(sK3,sK2)),
% 11.85/1.98    inference(cnf_transformation,[],[f42])).
% 11.85/1.98  
% 11.85/1.98  fof(f1,axiom,(
% 11.85/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f18,plain,(
% 11.85/1.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.85/1.98    inference(ennf_transformation,[],[f1])).
% 11.85/1.98  
% 11.85/1.98  fof(f43,plain,(
% 11.85/1.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f18])).
% 11.85/1.98  
% 11.85/1.98  fof(f12,axiom,(
% 11.85/1.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f63,plain,(
% 11.85/1.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.85/1.98    inference(cnf_transformation,[],[f12])).
% 11.85/1.98  
% 11.85/1.98  fof(f2,axiom,(
% 11.85/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f17,plain,(
% 11.85/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.85/1.98    inference(rectify,[],[f2])).
% 11.85/1.98  
% 11.85/1.98  fof(f19,plain,(
% 11.85/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.85/1.98    inference(ennf_transformation,[],[f17])).
% 11.85/1.98  
% 11.85/1.98  fof(f29,plain,(
% 11.85/1.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.85/1.98    introduced(choice_axiom,[])).
% 11.85/1.98  
% 11.85/1.98  fof(f30,plain,(
% 11.85/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.85/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f29])).
% 11.85/1.98  
% 11.85/1.98  fof(f45,plain,(
% 11.85/1.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f30])).
% 11.85/1.98  
% 11.85/1.98  fof(f8,axiom,(
% 11.85/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f22,plain,(
% 11.85/1.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(ennf_transformation,[],[f8])).
% 11.85/1.98  
% 11.85/1.98  fof(f33,plain,(
% 11.85/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(nnf_transformation,[],[f22])).
% 11.85/1.98  
% 11.85/1.98  fof(f34,plain,(
% 11.85/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(rectify,[],[f33])).
% 11.85/1.98  
% 11.85/1.98  fof(f35,plain,(
% 11.85/1.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 11.85/1.98    introduced(choice_axiom,[])).
% 11.85/1.98  
% 11.85/1.98  fof(f36,plain,(
% 11.85/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 11.85/1.98  
% 11.85/1.98  fof(f55,plain,(
% 11.85/1.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f36])).
% 11.85/1.98  
% 11.85/1.98  fof(f57,plain,(
% 11.85/1.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f36])).
% 11.85/1.98  
% 11.85/1.98  fof(f46,plain,(
% 11.85/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f30])).
% 11.85/1.98  
% 11.85/1.98  fof(f3,axiom,(
% 11.85/1.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f20,plain,(
% 11.85/1.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 11.85/1.98    inference(ennf_transformation,[],[f3])).
% 11.85/1.98  
% 11.85/1.98  fof(f48,plain,(
% 11.85/1.98    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 11.85/1.98    inference(cnf_transformation,[],[f20])).
% 11.85/1.98  
% 11.85/1.98  fof(f6,axiom,(
% 11.85/1.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f53,plain,(
% 11.85/1.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.85/1.98    inference(cnf_transformation,[],[f6])).
% 11.85/1.98  
% 11.85/1.98  fof(f69,plain,(
% 11.85/1.98    v1_relat_1(sK3)),
% 11.85/1.98    inference(cnf_transformation,[],[f42])).
% 11.85/1.98  
% 11.85/1.98  fof(f7,axiom,(
% 11.85/1.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f21,plain,(
% 11.85/1.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.85/1.98    inference(ennf_transformation,[],[f7])).
% 11.85/1.98  
% 11.85/1.98  fof(f54,plain,(
% 11.85/1.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f21])).
% 11.85/1.98  
% 11.85/1.98  fof(f10,axiom,(
% 11.85/1.98    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f24,plain,(
% 11.85/1.98    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.85/1.98    inference(ennf_transformation,[],[f10])).
% 11.85/1.98  
% 11.85/1.98  fof(f60,plain,(
% 11.85/1.98    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f24])).
% 11.85/1.98  
% 11.85/1.98  fof(f14,axiom,(
% 11.85/1.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f26,plain,(
% 11.85/1.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.85/1.98    inference(ennf_transformation,[],[f14])).
% 11.85/1.98  
% 11.85/1.98  fof(f27,plain,(
% 11.85/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.85/1.98    inference(flattening,[],[f26])).
% 11.85/1.98  
% 11.85/1.98  fof(f68,plain,(
% 11.85/1.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f27])).
% 11.85/1.98  
% 11.85/1.98  fof(f9,axiom,(
% 11.85/1.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f23,plain,(
% 11.85/1.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.85/1.98    inference(ennf_transformation,[],[f9])).
% 11.85/1.98  
% 11.85/1.98  fof(f59,plain,(
% 11.85/1.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f23])).
% 11.85/1.98  
% 11.85/1.98  fof(f64,plain,(
% 11.85/1.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.85/1.98    inference(cnf_transformation,[],[f12])).
% 11.85/1.98  
% 11.85/1.98  fof(f4,axiom,(
% 11.85/1.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f31,plain,(
% 11.85/1.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.85/1.98    inference(nnf_transformation,[],[f4])).
% 11.85/1.98  
% 11.85/1.98  fof(f32,plain,(
% 11.85/1.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.85/1.98    inference(flattening,[],[f31])).
% 11.85/1.98  
% 11.85/1.98  fof(f51,plain,(
% 11.85/1.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.85/1.98    inference(cnf_transformation,[],[f32])).
% 11.85/1.98  
% 11.85/1.98  fof(f73,plain,(
% 11.85/1.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.85/1.98    inference(equality_resolution,[],[f51])).
% 11.85/1.98  
% 11.85/1.98  fof(f5,axiom,(
% 11.85/1.98    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f52,plain,(
% 11.85/1.98    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 11.85/1.98    inference(cnf_transformation,[],[f5])).
% 11.85/1.98  
% 11.85/1.98  fof(f13,axiom,(
% 11.85/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f25,plain,(
% 11.85/1.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(ennf_transformation,[],[f13])).
% 11.85/1.98  
% 11.85/1.98  fof(f37,plain,(
% 11.85/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(nnf_transformation,[],[f25])).
% 11.85/1.98  
% 11.85/1.98  fof(f38,plain,(
% 11.85/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 11.85/1.98    inference(flattening,[],[f37])).
% 11.85/1.98  
% 11.85/1.98  fof(f67,plain,(
% 11.85/1.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f38])).
% 11.85/1.98  
% 11.85/1.98  fof(f44,plain,(
% 11.85/1.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f30])).
% 11.85/1.98  
% 11.85/1.98  fof(f47,plain,(
% 11.85/1.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f20])).
% 11.85/1.98  
% 11.85/1.98  fof(f72,plain,(
% 11.85/1.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 11.85/1.98    inference(equality_resolution,[],[f47])).
% 11.85/1.98  
% 11.85/1.98  fof(f50,plain,(
% 11.85/1.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.85/1.98    inference(cnf_transformation,[],[f32])).
% 11.85/1.98  
% 11.85/1.98  fof(f74,plain,(
% 11.85/1.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.85/1.98    inference(equality_resolution,[],[f50])).
% 11.85/1.98  
% 11.85/1.98  fof(f49,plain,(
% 11.85/1.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.85/1.98    inference(cnf_transformation,[],[f32])).
% 11.85/1.98  
% 11.85/1.98  fof(f11,axiom,(
% 11.85/1.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.85/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.85/1.98  
% 11.85/1.98  fof(f61,plain,(
% 11.85/1.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.85/1.98    inference(cnf_transformation,[],[f11])).
% 11.85/1.98  
% 11.85/1.98  fof(f71,plain,(
% 11.85/1.98    ~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k9_relat_1(sK3,sK2)),
% 11.85/1.98    inference(cnf_transformation,[],[f42])).
% 11.85/1.98  
% 11.85/1.98  cnf(c_27,negated_conjecture,
% 11.85/1.98      ( r1_xboole_0(k1_relat_1(sK3),sK2)
% 11.85/1.98      | k1_xboole_0 = k9_relat_1(sK3,sK2) ),
% 11.85/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1026,plain,
% 11.85/1.98      ( k1_xboole_0 = k9_relat_1(sK3,sK2)
% 11.85/1.98      | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_0,plain,
% 11.85/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.85/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1044,plain,
% 11.85/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.85/1.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_2040,plain,
% 11.85/1.98      ( k9_relat_1(sK3,sK2) = k1_xboole_0
% 11.85/1.98      | r1_xboole_0(sK2,k1_relat_1(sK3)) = iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_1026,c_1044]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_21,plain,
% 11.85/1.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.85/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_2,plain,
% 11.85/1.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 11.85/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1042,plain,
% 11.85/1.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 11.85/1.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_15,plain,
% 11.85/1.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 11.85/1.98      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 11.85/1.98      | ~ v1_relat_1(X1) ),
% 11.85/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1032,plain,
% 11.85/1.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 11.85/1.98      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 11.85/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_13,plain,
% 11.85/1.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 11.85/1.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 11.85/1.98      | ~ v1_relat_1(X1) ),
% 11.85/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1034,plain,
% 11.85/1.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 11.85/1.98      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 11.85/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1,plain,
% 11.85/1.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.85/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1043,plain,
% 11.85/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.85/1.98      | r2_hidden(X0,X2) != iProver_top
% 11.85/1.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_2868,plain,
% 11.85/1.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 11.85/1.98      | r2_hidden(sK1(X0,X2,X1),X3) != iProver_top
% 11.85/1.98      | r1_xboole_0(X3,X2) != iProver_top
% 11.85/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_1034,c_1043]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_10670,plain,
% 11.85/1.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 11.85/1.98      | r1_xboole_0(k1_relat_1(X1),X2) != iProver_top
% 11.85/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_1032,c_2868]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_28376,plain,
% 11.85/1.98      ( r1_xboole_0(X0,k9_relat_1(X1,X2)) = iProver_top
% 11.85/1.98      | r1_xboole_0(k1_relat_1(X1),X2) != iProver_top
% 11.85/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_1042,c_10670]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_4,plain,
% 11.85/1.98      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 11.85/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_1040,plain,
% 11.85/1.98      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_29756,plain,
% 11.85/1.98      ( k9_relat_1(X0,X1) = k1_xboole_0
% 11.85/1.98      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 11.85/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_28376,c_1040]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_32860,plain,
% 11.85/1.98      ( k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
% 11.85/1.98      | r1_xboole_0(X0,X1) != iProver_top
% 11.85/1.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_21,c_29756]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_10,plain,
% 11.85/1.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.85/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_67,plain,
% 11.85/1.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_33094,plain,
% 11.85/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.85/1.98      | k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0 ),
% 11.85/1.98      inference(global_propositional_subsumption,
% 11.85/1.98                [status(thm)],
% 11.85/1.98                [c_32860,c_67]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_33095,plain,
% 11.85/1.98      ( k9_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
% 11.85/1.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.85/1.98      inference(renaming,[status(thm)],[c_33094]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_33100,plain,
% 11.85/1.98      ( k9_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = k1_xboole_0
% 11.85/1.98      | k9_relat_1(sK3,sK2) = k1_xboole_0 ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_2040,c_33095]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_28,negated_conjecture,
% 11.85/1.98      ( v1_relat_1(sK3) ),
% 11.85/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_29,plain,
% 11.85/1.98      ( v1_relat_1(sK3) = iProver_top ),
% 11.85/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_2043,plain,
% 11.85/1.98      ( k9_relat_1(sK3,sK2) = k1_xboole_0
% 11.85/1.98      | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_2040,c_1044]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_32828,plain,
% 11.85/1.98      ( k9_relat_1(sK3,sK2) = k1_xboole_0
% 11.85/1.98      | v1_relat_1(sK3) != iProver_top ),
% 11.85/1.98      inference(superposition,[status(thm)],[c_2043,c_29756]) ).
% 11.85/1.98  
% 11.85/1.98  cnf(c_33397,plain,
% 11.85/1.98      ( k9_relat_1(sK3,sK2) = k1_xboole_0 ),
% 11.85/1.98      inference(global_propositional_subsumption,
% 11.85/1.98                [status(thm)],
% 11.85/1.98                [c_33100,c_29,c_32828]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1025,plain,
% 11.85/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_11,plain,
% 11.85/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1036,plain,
% 11.85/1.99      ( v1_relat_1(X0) != iProver_top
% 11.85/1.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_17,plain,
% 11.85/1.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 11.85/1.99      | ~ v1_relat_1(X0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_25,plain,
% 11.85/1.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.85/1.99      | ~ v1_relat_1(X0)
% 11.85/1.99      | k7_relat_1(X0,X1) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_314,plain,
% 11.85/1.99      ( ~ v1_relat_1(X0)
% 11.85/1.99      | ~ v1_relat_1(X1)
% 11.85/1.99      | k7_relat_1(X0,X2) = X0
% 11.85/1.99      | k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) != X2
% 11.85/1.99      | k1_relat_1(X0) != X1 ),
% 11.85/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_315,plain,
% 11.85/1.99      ( ~ v1_relat_1(X0)
% 11.85/1.99      | ~ v1_relat_1(k1_relat_1(X0))
% 11.85/1.99      | k7_relat_1(X0,k2_zfmisc_1(k1_relat_1(k1_relat_1(X0)),k2_relat_1(k1_relat_1(X0)))) = X0 ),
% 11.85/1.99      inference(unflattening,[status(thm)],[c_314]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1024,plain,
% 11.85/1.99      ( k7_relat_1(X0,k2_zfmisc_1(k1_relat_1(k1_relat_1(X0)),k2_relat_1(k1_relat_1(X0)))) = X0
% 11.85/1.99      | v1_relat_1(X0) != iProver_top
% 11.85/1.99      | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1364,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k1_relat_1(k6_relat_1(X0))),k2_relat_1(k1_relat_1(k6_relat_1(X0))))) = k6_relat_1(X0)
% 11.85/1.99      | v1_relat_1(X0) != iProver_top
% 11.85/1.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_21,c_1024]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1365,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0)
% 11.85/1.99      | v1_relat_1(X0) != iProver_top
% 11.85/1.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_1364,c_21]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3799,plain,
% 11.85/1.99      ( v1_relat_1(X0) != iProver_top
% 11.85/1.99      | k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0) ),
% 11.85/1.99      inference(global_propositional_subsumption,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_1365,c_67]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3800,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k6_relat_1(X0)
% 11.85/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.85/1.99      inference(renaming,[status(thm)],[c_3799]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3806,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(k7_relat_1(X0,X1)),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) = k6_relat_1(k7_relat_1(X0,X1))
% 11.85/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1036,c_3800]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_15849,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(k7_relat_1(sK3,X0)))) = k6_relat_1(k7_relat_1(sK3,X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1025,c_3806]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_16,plain,
% 11.85/1.99      ( ~ v1_relat_1(X0)
% 11.85/1.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1031,plain,
% 11.85/1.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.85/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2215,plain,
% 11.85/1.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1025,c_1031]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_15853,plain,
% 11.85/1.99      ( k7_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k6_relat_1(k7_relat_1(sK3,X0)) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_15849,c_2215]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1037,plain,
% 11.85/1.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2213,plain,
% 11.85/1.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1037,c_1031]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_16290,plain,
% 11.85/1.99      ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k2_relat_1(k6_relat_1(k7_relat_1(sK3,X0))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_15853,c_2213]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_20,plain,
% 11.85/1.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_16307,plain,
% 11.85/1.99      ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_16290,c_20]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33410,plain,
% 11.85/1.99      ( k9_relat_1(k6_relat_1(k7_relat_1(sK3,sK2)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0)) = k7_relat_1(sK3,sK2) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_33397,c_16307]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6,plain,
% 11.85/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9,plain,
% 11.85/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1038,plain,
% 11.85/1.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1628,plain,
% 11.85/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6,c_1038]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2871,plain,
% 11.85/1.99      ( r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) != iProver_top
% 11.85/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1034,c_1628]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3164,plain,
% 11.85/1.99      ( r1_xboole_0(X0,k9_relat_1(X1,k1_xboole_0)) = iProver_top
% 11.85/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1042,c_2871]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3296,plain,
% 11.85/1.99      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.85/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3164,c_1040]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3301,plain,
% 11.85/1.99      ( k9_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1037,c_3296]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33435,plain,
% 11.85/1.99      ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_33410,c_6,c_3301]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_22542,plain,
% 11.85/1.99      ( ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),X0)
% 11.85/1.99      | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | ~ r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK3,sK2))) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_31120,plain,
% 11.85/1.99      ( ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_22542]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_534,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_13895,plain,
% 11.85/1.99      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_534]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_13896,plain,
% 11.85/1.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.85/1.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 11.85/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_13895]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_535,plain,
% 11.85/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.85/1.99      theory(equality) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6836,plain,
% 11.85/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.85/1.99      | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) != X1
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) != X0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_535]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6838,plain,
% 11.85/1.99      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_6836]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_22,plain,
% 11.85/1.99      ( ~ r2_hidden(X0,X1)
% 11.85/1.99      | ~ r2_hidden(X0,k1_relat_1(X2))
% 11.85/1.99      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 11.85/1.99      | ~ v1_relat_1(X2) ),
% 11.85/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1237,plain,
% 11.85/1.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 11.85/1.99      | ~ r2_hidden(X0,sK2)
% 11.85/1.99      | ~ v1_relat_1(sK3) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5636,plain,
% 11.85/1.99      ( r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))
% 11.85/1.99      | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
% 11.85/1.99      | ~ r2_hidden(sK0(k1_relat_1(sK3),sK2),sK2)
% 11.85/1.99      | ~ v1_relat_1(sK3) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1237]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_542,plain,
% 11.85/1.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 11.85/1.99      theory(equality) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2404,plain,
% 11.85/1.99      ( k7_relat_1(sK3,sK2) != X0
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relat_1(X0) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_542]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2405,plain,
% 11.85/1.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_2404]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1486,plain,
% 11.85/1.99      ( X0 != X1
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) != X1
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) = X0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_534]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1900,plain,
% 11.85/1.99      ( X0 != k1_relat_1(X1)
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) = X0
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) != k1_relat_1(X1) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1486]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1901,plain,
% 11.85/1.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_relat_1(k1_xboole_0)
% 11.85/1.99      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
% 11.85/1.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1900]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1093,plain,
% 11.85/1.99      ( k9_relat_1(sK3,sK2) != X0
% 11.85/1.99      | k1_xboole_0 != X0
% 11.85/1.99      | k1_xboole_0 = k9_relat_1(sK3,sK2) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_534]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1094,plain,
% 11.85/1.99      ( k9_relat_1(sK3,sK2) != k1_xboole_0
% 11.85/1.99      | k1_xboole_0 = k9_relat_1(sK3,sK2)
% 11.85/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1093]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1072,plain,
% 11.85/1.99      ( r2_hidden(sK0(k1_relat_1(sK3),sK2),sK2)
% 11.85/1.99      | r1_xboole_0(k1_relat_1(sK3),sK2) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3,plain,
% 11.85/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1073,plain,
% 11.85/1.99      ( r2_hidden(sK0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
% 11.85/1.99      | r1_xboole_0(k1_relat_1(sK3),sK2) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5,plain,
% 11.85/1.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7,plain,
% 11.85/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_74,plain,
% 11.85/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_8,plain,
% 11.85/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.85/1.99      | k1_xboole_0 = X0
% 11.85/1.99      | k1_xboole_0 = X1 ),
% 11.85/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_73,plain,
% 11.85/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.85/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_19,plain,
% 11.85/1.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_26,negated_conjecture,
% 11.85/1.99      ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
% 11.85/1.99      | k1_xboole_0 != k9_relat_1(sK3,sK2) ),
% 11.85/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(contradiction,plain,
% 11.85/1.99      ( $false ),
% 11.85/1.99      inference(minisat,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_33435,c_32828,c_31120,c_13896,c_6838,c_5636,c_2405,
% 11.85/1.99                 c_1901,c_1094,c_1072,c_1073,c_5,c_74,c_73,c_19,c_26,
% 11.85/1.99                 c_29,c_28]) ).
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  ------                               Statistics
% 11.85/1.99  
% 11.85/1.99  ------ General
% 11.85/1.99  
% 11.85/1.99  abstr_ref_over_cycles:                  0
% 11.85/1.99  abstr_ref_under_cycles:                 0
% 11.85/1.99  gc_basic_clause_elim:                   0
% 11.85/1.99  forced_gc_time:                         0
% 11.85/1.99  parsing_time:                           0.008
% 11.85/1.99  unif_index_cands_time:                  0.
% 11.85/1.99  unif_index_add_time:                    0.
% 11.85/1.99  orderings_time:                         0.
% 11.85/1.99  out_proof_time:                         0.013
% 11.85/1.99  total_time:                             1.379
% 11.85/1.99  num_of_symbols:                         47
% 11.85/1.99  num_of_terms:                           61173
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing
% 11.85/1.99  
% 11.85/1.99  num_of_splits:                          0
% 11.85/1.99  num_of_split_atoms:                     0
% 11.85/1.99  num_of_reused_defs:                     0
% 11.85/1.99  num_eq_ax_congr_red:                    25
% 11.85/1.99  num_of_sem_filtered_clauses:            1
% 11.85/1.99  num_of_subtypes:                        0
% 11.85/1.99  monotx_restored_types:                  0
% 11.85/1.99  sat_num_of_epr_types:                   0
% 11.85/1.99  sat_num_of_non_cyclic_types:            0
% 11.85/1.99  sat_guarded_non_collapsed_types:        0
% 11.85/1.99  num_pure_diseq_elim:                    0
% 11.85/1.99  simp_replaced_by:                       0
% 11.85/1.99  res_preprocessed:                       136
% 11.85/1.99  prep_upred:                             0
% 11.85/1.99  prep_unflattend:                        2
% 11.85/1.99  smt_new_axioms:                         0
% 11.85/1.99  pred_elim_cands:                        3
% 11.85/1.99  pred_elim:                              1
% 11.85/1.99  pred_elim_cl:                           1
% 11.85/1.99  pred_elim_cycles:                       3
% 11.85/1.99  merged_defs:                            8
% 11.85/1.99  merged_defs_ncl:                        0
% 11.85/1.99  bin_hyper_res:                          8
% 11.85/1.99  prep_cycles:                            4
% 11.85/1.99  pred_elim_time:                         0.001
% 11.85/1.99  splitting_time:                         0.
% 11.85/1.99  sem_filter_time:                        0.
% 11.85/1.99  monotx_time:                            0.
% 11.85/1.99  subtype_inf_time:                       0.
% 11.85/1.99  
% 11.85/1.99  ------ Problem properties
% 11.85/1.99  
% 11.85/1.99  clauses:                                28
% 11.85/1.99  conjectures:                            3
% 11.85/1.99  epr:                                    5
% 11.85/1.99  horn:                                   24
% 11.85/1.99  ground:                                 6
% 11.85/1.99  unary:                                  10
% 11.85/1.99  binary:                                 8
% 11.85/1.99  lits:                                   59
% 11.85/1.99  lits_eq:                                14
% 11.85/1.99  fd_pure:                                0
% 11.85/1.99  fd_pseudo:                              0
% 11.85/1.99  fd_cond:                                2
% 11.85/1.99  fd_pseudo_cond:                         0
% 11.85/1.99  ac_symbols:                             0
% 11.85/1.99  
% 11.85/1.99  ------ Propositional Solver
% 11.85/1.99  
% 11.85/1.99  prop_solver_calls:                      35
% 11.85/1.99  prop_fast_solver_calls:                 2366
% 11.85/1.99  smt_solver_calls:                       0
% 11.85/1.99  smt_fast_solver_calls:                  0
% 11.85/1.99  prop_num_of_clauses:                    17824
% 11.85/1.99  prop_preprocess_simplified:             23161
% 11.85/1.99  prop_fo_subsumed:                       114
% 11.85/1.99  prop_solver_time:                       0.
% 11.85/1.99  smt_solver_time:                        0.
% 11.85/1.99  smt_fast_solver_time:                   0.
% 11.85/1.99  prop_fast_solver_time:                  0.
% 11.85/1.99  prop_unsat_core_time:                   0.002
% 11.85/1.99  
% 11.85/1.99  ------ QBF
% 11.85/1.99  
% 11.85/1.99  qbf_q_res:                              0
% 11.85/1.99  qbf_num_tautologies:                    0
% 11.85/1.99  qbf_prep_cycles:                        0
% 11.85/1.99  
% 11.85/1.99  ------ BMC1
% 11.85/1.99  
% 11.85/1.99  bmc1_current_bound:                     -1
% 11.85/1.99  bmc1_last_solved_bound:                 -1
% 11.85/1.99  bmc1_unsat_core_size:                   -1
% 11.85/1.99  bmc1_unsat_core_parents_size:           -1
% 11.85/1.99  bmc1_merge_next_fun:                    0
% 11.85/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation
% 11.85/1.99  
% 11.85/1.99  inst_num_of_clauses:                    3872
% 11.85/1.99  inst_num_in_passive:                    1232
% 11.85/1.99  inst_num_in_active:                     1624
% 11.85/1.99  inst_num_in_unprocessed:                1017
% 11.85/1.99  inst_num_of_loops:                      2040
% 11.85/1.99  inst_num_of_learning_restarts:          0
% 11.85/1.99  inst_num_moves_active_passive:          412
% 11.85/1.99  inst_lit_activity:                      0
% 11.85/1.99  inst_lit_activity_moves:                0
% 11.85/1.99  inst_num_tautologies:                   0
% 11.85/1.99  inst_num_prop_implied:                  0
% 11.85/1.99  inst_num_existing_simplified:           0
% 11.85/1.99  inst_num_eq_res_simplified:             0
% 11.85/1.99  inst_num_child_elim:                    0
% 11.85/1.99  inst_num_of_dismatching_blockings:      1070
% 11.85/1.99  inst_num_of_non_proper_insts:           3817
% 11.85/1.99  inst_num_of_duplicates:                 0
% 11.85/1.99  inst_inst_num_from_inst_to_res:         0
% 11.85/1.99  inst_dismatching_checking_time:         0.
% 11.85/1.99  
% 11.85/1.99  ------ Resolution
% 11.85/1.99  
% 11.85/1.99  res_num_of_clauses:                     0
% 11.85/1.99  res_num_in_passive:                     0
% 11.85/1.99  res_num_in_active:                      0
% 11.85/1.99  res_num_of_loops:                       140
% 11.85/1.99  res_forward_subset_subsumed:            112
% 11.85/1.99  res_backward_subset_subsumed:           10
% 11.85/1.99  res_forward_subsumed:                   0
% 11.85/1.99  res_backward_subsumed:                  0
% 11.85/1.99  res_forward_subsumption_resolution:     0
% 11.85/1.99  res_backward_subsumption_resolution:    0
% 11.85/1.99  res_clause_to_clause_subsumption:       12426
% 11.85/1.99  res_orphan_elimination:                 0
% 11.85/1.99  res_tautology_del:                      309
% 11.85/1.99  res_num_eq_res_simplified:              0
% 11.85/1.99  res_num_sel_changes:                    0
% 11.85/1.99  res_moves_from_active_to_pass:          0
% 11.85/1.99  
% 11.85/1.99  ------ Superposition
% 11.85/1.99  
% 11.85/1.99  sup_time_total:                         0.
% 11.85/1.99  sup_time_generating:                    0.
% 11.85/1.99  sup_time_sim_full:                      0.
% 11.85/1.99  sup_time_sim_immed:                     0.
% 11.85/1.99  
% 11.85/1.99  sup_num_of_clauses:                     1821
% 11.85/1.99  sup_num_in_active:                      324
% 11.85/1.99  sup_num_in_passive:                     1497
% 11.85/1.99  sup_num_of_loops:                       406
% 11.85/1.99  sup_fw_superposition:                   2266
% 11.85/1.99  sup_bw_superposition:                   1917
% 11.85/1.99  sup_immediate_simplified:               2129
% 11.85/1.99  sup_given_eliminated:                   39
% 11.85/1.99  comparisons_done:                       0
% 11.85/1.99  comparisons_avoided:                    0
% 11.85/1.99  
% 11.85/1.99  ------ Simplifications
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  sim_fw_subset_subsumed:                 371
% 11.85/1.99  sim_bw_subset_subsumed:                 19
% 11.85/1.99  sim_fw_subsumed:                        1038
% 11.85/1.99  sim_bw_subsumed:                        91
% 11.85/1.99  sim_fw_subsumption_res:                 0
% 11.85/1.99  sim_bw_subsumption_res:                 0
% 11.85/1.99  sim_tautology_del:                      78
% 11.85/1.99  sim_eq_tautology_del:                   58
% 11.85/1.99  sim_eq_res_simp:                        1
% 11.85/1.99  sim_fw_demodulated:                     996
% 11.85/1.99  sim_bw_demodulated:                     51
% 11.85/1.99  sim_light_normalised:                   555
% 11.85/1.99  sim_joinable_taut:                      0
% 11.85/1.99  sim_joinable_simp:                      0
% 11.85/1.99  sim_ac_normalised:                      0
% 11.85/1.99  sim_smt_subsumption:                    0
% 11.85/1.99  
%------------------------------------------------------------------------------
