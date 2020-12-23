%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:31 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 408 expanded)
%              Number of clauses        :   68 ( 150 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  430 (1477 expanded)
%              Number of equality atoms :  229 ( 783 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK8(X0,X1))
        & k1_relat_1(sK8(X0,X1)) = X0
        & v1_funct_1(sK8(X0,X1))
        & v1_relat_1(sK8(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK8(X0,X1))
          & k1_relat_1(sK8(X0,X1)) = X0
          & v1_funct_1(sK8(X0,X1))
          & v1_relat_1(sK8(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK8(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK8(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK9)
          | k1_relat_1(X2) != sK10
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK10
        | k1_xboole_0 != sK9 ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK9)
        | k1_relat_1(X2) != sK10
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK10
      | k1_xboole_0 != sK9 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f19,f43])).

fof(f73,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK9)
      | k1_relat_1(X2) != sK10
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK8(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK8(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK3(X4),sK4(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK3(X4),sK4(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f33,f32])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( k1_xboole_0 = sK10
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1293,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK5(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1298,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2014,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1298])).

cnf(c_3371,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_2014])).

cnf(c_20,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3374,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3371,c_20])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1305,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1299,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2266,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1299])).

cnf(c_23,plain,
    ( k2_relat_1(sK8(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,plain,
    ( k1_relat_1(sK8(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK9)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK10 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1288,plain,
    ( k1_relat_1(X0) != sK10
    | r1_tarski(k2_relat_1(X0),sK9) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1561,plain,
    ( sK10 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK8(X0,X1)),sK9) != iProver_top
    | v1_funct_1(sK8(X0,X1)) != iProver_top
    | v1_relat_1(sK8(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1288])).

cnf(c_26,plain,
    ( v1_relat_1(sK8(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK8(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( v1_funct_1(sK8(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK8(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1782,plain,
    ( sK10 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK8(X0,X1)),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_32,c_35])).

cnf(c_1789,plain,
    ( sK10 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK8(sK10,X0)),sK9) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1782])).

cnf(c_1923,plain,
    ( sK10 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1789])).

cnf(c_5765,plain,
    ( sK0(k1_tarski(X0),sK9) = X0
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2266,c_1923])).

cnf(c_21,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_253,plain,
    ( v1_funct_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_254,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_687,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK9)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK10
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_254])).

cnf(c_688,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK9)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK10 ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_41,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_374,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK10
    | k2_relat_1(X0) != k1_xboole_0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_375,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK10
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK10
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_690,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_41,c_20,c_3,c_377])).

cnf(c_692,plain,
    ( k1_relat_1(k1_xboole_0) != sK10
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_918,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1549,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(X0) = sK10
    | sK10 != X1 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1550,plain,
    ( k1_relat_1(k1_xboole_0) = sK10
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK10 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1296,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2224,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_2014])).

cnf(c_6490,plain,
    ( sK0(k1_tarski(X0),sK9) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5765,c_21,c_692,c_1550,c_2224])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1306,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6494,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r1_tarski(k1_tarski(X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6490,c_1306])).

cnf(c_6504,plain,
    ( r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6494,c_21,c_692,c_1550,c_1923,c_2224])).

cnf(c_6516,plain,
    ( sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3374,c_6504])).

cnf(c_1690,plain,
    ( X0 != X1
    | sK10 != X1
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_2025,plain,
    ( X0 != sK10
    | sK10 = X0
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2027,plain,
    ( sK10 != sK10
    | sK10 = k1_xboole_0
    | k1_xboole_0 != sK10 ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1998,plain,
    ( r2_hidden(sK10,k1_tarski(sK10)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1691,plain,
    ( ~ r2_hidden(sK10,k1_tarski(X0))
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1997,plain,
    ( ~ r2_hidden(sK10,k1_tarski(sK10))
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_1525,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1526,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_64,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_63,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 = sK10
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6516,c_2224,c_2027,c_1998,c_1997,c_1550,c_1526,c_692,c_64,c_63,c_21,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.84/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.02  
% 2.84/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/1.02  
% 2.84/1.02  ------  iProver source info
% 2.84/1.02  
% 2.84/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.84/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/1.02  git: non_committed_changes: false
% 2.84/1.02  git: last_make_outside_of_git: false
% 2.84/1.02  
% 2.84/1.02  ------ 
% 2.84/1.02  
% 2.84/1.02  ------ Input Options
% 2.84/1.02  
% 2.84/1.02  --out_options                           all
% 2.84/1.02  --tptp_safe_out                         true
% 2.84/1.02  --problem_path                          ""
% 2.84/1.02  --include_path                          ""
% 2.84/1.02  --clausifier                            res/vclausify_rel
% 2.84/1.02  --clausifier_options                    --mode clausify
% 2.84/1.02  --stdin                                 false
% 2.84/1.02  --stats_out                             all
% 2.84/1.02  
% 2.84/1.02  ------ General Options
% 2.84/1.02  
% 2.84/1.02  --fof                                   false
% 2.84/1.02  --time_out_real                         305.
% 2.84/1.02  --time_out_virtual                      -1.
% 2.84/1.02  --symbol_type_check                     false
% 2.84/1.02  --clausify_out                          false
% 2.84/1.02  --sig_cnt_out                           false
% 2.84/1.02  --trig_cnt_out                          false
% 2.84/1.02  --trig_cnt_out_tolerance                1.
% 2.84/1.02  --trig_cnt_out_sk_spl                   false
% 2.84/1.02  --abstr_cl_out                          false
% 2.84/1.02  
% 2.84/1.02  ------ Global Options
% 2.84/1.02  
% 2.84/1.02  --schedule                              default
% 2.84/1.02  --add_important_lit                     false
% 2.84/1.02  --prop_solver_per_cl                    1000
% 2.84/1.02  --min_unsat_core                        false
% 2.84/1.02  --soft_assumptions                      false
% 2.84/1.02  --soft_lemma_size                       3
% 2.84/1.02  --prop_impl_unit_size                   0
% 2.84/1.02  --prop_impl_unit                        []
% 2.84/1.02  --share_sel_clauses                     true
% 2.84/1.02  --reset_solvers                         false
% 2.84/1.02  --bc_imp_inh                            [conj_cone]
% 2.84/1.02  --conj_cone_tolerance                   3.
% 2.84/1.02  --extra_neg_conj                        none
% 2.84/1.02  --large_theory_mode                     true
% 2.84/1.02  --prolific_symb_bound                   200
% 2.84/1.02  --lt_threshold                          2000
% 2.84/1.02  --clause_weak_htbl                      true
% 2.84/1.02  --gc_record_bc_elim                     false
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing Options
% 2.84/1.02  
% 2.84/1.02  --preprocessing_flag                    true
% 2.84/1.02  --time_out_prep_mult                    0.1
% 2.84/1.02  --splitting_mode                        input
% 2.84/1.02  --splitting_grd                         true
% 2.84/1.02  --splitting_cvd                         false
% 2.84/1.02  --splitting_cvd_svl                     false
% 2.84/1.02  --splitting_nvd                         32
% 2.84/1.02  --sub_typing                            true
% 2.84/1.02  --prep_gs_sim                           true
% 2.84/1.02  --prep_unflatten                        true
% 2.84/1.02  --prep_res_sim                          true
% 2.84/1.02  --prep_upred                            true
% 2.84/1.02  --prep_sem_filter                       exhaustive
% 2.84/1.02  --prep_sem_filter_out                   false
% 2.84/1.02  --pred_elim                             true
% 2.84/1.02  --res_sim_input                         true
% 2.84/1.02  --eq_ax_congr_red                       true
% 2.84/1.02  --pure_diseq_elim                       true
% 2.84/1.02  --brand_transform                       false
% 2.84/1.02  --non_eq_to_eq                          false
% 2.84/1.02  --prep_def_merge                        true
% 2.84/1.02  --prep_def_merge_prop_impl              false
% 2.84/1.02  --prep_def_merge_mbd                    true
% 2.84/1.02  --prep_def_merge_tr_red                 false
% 2.84/1.02  --prep_def_merge_tr_cl                  false
% 2.84/1.02  --smt_preprocessing                     true
% 2.84/1.02  --smt_ac_axioms                         fast
% 2.84/1.02  --preprocessed_out                      false
% 2.84/1.02  --preprocessed_stats                    false
% 2.84/1.02  
% 2.84/1.02  ------ Abstraction refinement Options
% 2.84/1.02  
% 2.84/1.02  --abstr_ref                             []
% 2.84/1.02  --abstr_ref_prep                        false
% 2.84/1.02  --abstr_ref_until_sat                   false
% 2.84/1.02  --abstr_ref_sig_restrict                funpre
% 2.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.02  --abstr_ref_under                       []
% 2.84/1.02  
% 2.84/1.02  ------ SAT Options
% 2.84/1.02  
% 2.84/1.02  --sat_mode                              false
% 2.84/1.02  --sat_fm_restart_options                ""
% 2.84/1.02  --sat_gr_def                            false
% 2.84/1.02  --sat_epr_types                         true
% 2.84/1.02  --sat_non_cyclic_types                  false
% 2.84/1.02  --sat_finite_models                     false
% 2.84/1.02  --sat_fm_lemmas                         false
% 2.84/1.02  --sat_fm_prep                           false
% 2.84/1.02  --sat_fm_uc_incr                        true
% 2.84/1.02  --sat_out_model                         small
% 2.84/1.02  --sat_out_clauses                       false
% 2.84/1.02  
% 2.84/1.02  ------ QBF Options
% 2.84/1.02  
% 2.84/1.02  --qbf_mode                              false
% 2.84/1.02  --qbf_elim_univ                         false
% 2.84/1.02  --qbf_dom_inst                          none
% 2.84/1.02  --qbf_dom_pre_inst                      false
% 2.84/1.02  --qbf_sk_in                             false
% 2.84/1.02  --qbf_pred_elim                         true
% 2.84/1.02  --qbf_split                             512
% 2.84/1.02  
% 2.84/1.02  ------ BMC1 Options
% 2.84/1.02  
% 2.84/1.02  --bmc1_incremental                      false
% 2.84/1.02  --bmc1_axioms                           reachable_all
% 2.84/1.02  --bmc1_min_bound                        0
% 2.84/1.02  --bmc1_max_bound                        -1
% 2.84/1.02  --bmc1_max_bound_default                -1
% 2.84/1.02  --bmc1_symbol_reachability              true
% 2.84/1.02  --bmc1_property_lemmas                  false
% 2.84/1.02  --bmc1_k_induction                      false
% 2.84/1.02  --bmc1_non_equiv_states                 false
% 2.84/1.02  --bmc1_deadlock                         false
% 2.84/1.02  --bmc1_ucm                              false
% 2.84/1.02  --bmc1_add_unsat_core                   none
% 2.84/1.02  --bmc1_unsat_core_children              false
% 2.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.02  --bmc1_out_stat                         full
% 2.84/1.02  --bmc1_ground_init                      false
% 2.84/1.02  --bmc1_pre_inst_next_state              false
% 2.84/1.02  --bmc1_pre_inst_state                   false
% 2.84/1.02  --bmc1_pre_inst_reach_state             false
% 2.84/1.02  --bmc1_out_unsat_core                   false
% 2.84/1.02  --bmc1_aig_witness_out                  false
% 2.84/1.02  --bmc1_verbose                          false
% 2.84/1.02  --bmc1_dump_clauses_tptp                false
% 2.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.02  --bmc1_dump_file                        -
% 2.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.02  --bmc1_ucm_extend_mode                  1
% 2.84/1.02  --bmc1_ucm_init_mode                    2
% 2.84/1.02  --bmc1_ucm_cone_mode                    none
% 2.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.02  --bmc1_ucm_relax_model                  4
% 2.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.02  --bmc1_ucm_layered_model                none
% 2.84/1.02  --bmc1_ucm_max_lemma_size               10
% 2.84/1.02  
% 2.84/1.02  ------ AIG Options
% 2.84/1.02  
% 2.84/1.02  --aig_mode                              false
% 2.84/1.02  
% 2.84/1.02  ------ Instantiation Options
% 2.84/1.02  
% 2.84/1.02  --instantiation_flag                    true
% 2.84/1.02  --inst_sos_flag                         false
% 2.84/1.02  --inst_sos_phase                        true
% 2.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.02  --inst_lit_sel_side                     num_symb
% 2.84/1.02  --inst_solver_per_active                1400
% 2.84/1.02  --inst_solver_calls_frac                1.
% 2.84/1.02  --inst_passive_queue_type               priority_queues
% 2.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.02  --inst_passive_queues_freq              [25;2]
% 2.84/1.02  --inst_dismatching                      true
% 2.84/1.02  --inst_eager_unprocessed_to_passive     true
% 2.84/1.02  --inst_prop_sim_given                   true
% 2.84/1.02  --inst_prop_sim_new                     false
% 2.84/1.02  --inst_subs_new                         false
% 2.84/1.02  --inst_eq_res_simp                      false
% 2.84/1.02  --inst_subs_given                       false
% 2.84/1.02  --inst_orphan_elimination               true
% 2.84/1.02  --inst_learning_loop_flag               true
% 2.84/1.02  --inst_learning_start                   3000
% 2.84/1.02  --inst_learning_factor                  2
% 2.84/1.02  --inst_start_prop_sim_after_learn       3
% 2.84/1.02  --inst_sel_renew                        solver
% 2.84/1.02  --inst_lit_activity_flag                true
% 2.84/1.02  --inst_restr_to_given                   false
% 2.84/1.02  --inst_activity_threshold               500
% 2.84/1.02  --inst_out_proof                        true
% 2.84/1.02  
% 2.84/1.02  ------ Resolution Options
% 2.84/1.02  
% 2.84/1.02  --resolution_flag                       true
% 2.84/1.02  --res_lit_sel                           adaptive
% 2.84/1.02  --res_lit_sel_side                      none
% 2.84/1.02  --res_ordering                          kbo
% 2.84/1.02  --res_to_prop_solver                    active
% 2.84/1.02  --res_prop_simpl_new                    false
% 2.84/1.02  --res_prop_simpl_given                  true
% 2.84/1.02  --res_passive_queue_type                priority_queues
% 2.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.02  --res_passive_queues_freq               [15;5]
% 2.84/1.02  --res_forward_subs                      full
% 2.84/1.02  --res_backward_subs                     full
% 2.84/1.02  --res_forward_subs_resolution           true
% 2.84/1.02  --res_backward_subs_resolution          true
% 2.84/1.02  --res_orphan_elimination                true
% 2.84/1.02  --res_time_limit                        2.
% 2.84/1.02  --res_out_proof                         true
% 2.84/1.02  
% 2.84/1.02  ------ Superposition Options
% 2.84/1.02  
% 2.84/1.02  --superposition_flag                    true
% 2.84/1.02  --sup_passive_queue_type                priority_queues
% 2.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.02  --demod_completeness_check              fast
% 2.84/1.02  --demod_use_ground                      true
% 2.84/1.02  --sup_to_prop_solver                    passive
% 2.84/1.02  --sup_prop_simpl_new                    true
% 2.84/1.02  --sup_prop_simpl_given                  true
% 2.84/1.02  --sup_fun_splitting                     false
% 2.84/1.02  --sup_smt_interval                      50000
% 2.84/1.02  
% 2.84/1.02  ------ Superposition Simplification Setup
% 2.84/1.02  
% 2.84/1.02  --sup_indices_passive                   []
% 2.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_full_bw                           [BwDemod]
% 2.84/1.02  --sup_immed_triv                        [TrivRules]
% 2.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_immed_bw_main                     []
% 2.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.02  
% 2.84/1.02  ------ Combination Options
% 2.84/1.02  
% 2.84/1.02  --comb_res_mult                         3
% 2.84/1.02  --comb_sup_mult                         2
% 2.84/1.02  --comb_inst_mult                        10
% 2.84/1.02  
% 2.84/1.02  ------ Debug Options
% 2.84/1.02  
% 2.84/1.02  --dbg_backtrace                         false
% 2.84/1.02  --dbg_dump_prop_clauses                 false
% 2.84/1.02  --dbg_dump_prop_clauses_file            -
% 2.84/1.02  --dbg_out_stat                          false
% 2.84/1.02  ------ Parsing...
% 2.84/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/1.02  ------ Proving...
% 2.84/1.02  ------ Problem Properties 
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  clauses                                 28
% 2.84/1.02  conjectures                             2
% 2.84/1.02  EPR                                     4
% 2.84/1.02  Horn                                    19
% 2.84/1.02  unary                                   8
% 2.84/1.02  binary                                  12
% 2.84/1.02  lits                                    57
% 2.84/1.02  lits eq                                 25
% 2.84/1.02  fd_pure                                 0
% 2.84/1.02  fd_pseudo                               0
% 2.84/1.02  fd_cond                                 4
% 2.84/1.02  fd_pseudo_cond                          4
% 2.84/1.02  AC symbols                              0
% 2.84/1.02  
% 2.84/1.02  ------ Schedule dynamic 5 is on 
% 2.84/1.02  
% 2.84/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  ------ 
% 2.84/1.02  Current options:
% 2.84/1.02  ------ 
% 2.84/1.02  
% 2.84/1.02  ------ Input Options
% 2.84/1.02  
% 2.84/1.02  --out_options                           all
% 2.84/1.02  --tptp_safe_out                         true
% 2.84/1.02  --problem_path                          ""
% 2.84/1.02  --include_path                          ""
% 2.84/1.02  --clausifier                            res/vclausify_rel
% 2.84/1.02  --clausifier_options                    --mode clausify
% 2.84/1.02  --stdin                                 false
% 2.84/1.02  --stats_out                             all
% 2.84/1.02  
% 2.84/1.02  ------ General Options
% 2.84/1.02  
% 2.84/1.02  --fof                                   false
% 2.84/1.02  --time_out_real                         305.
% 2.84/1.02  --time_out_virtual                      -1.
% 2.84/1.02  --symbol_type_check                     false
% 2.84/1.02  --clausify_out                          false
% 2.84/1.02  --sig_cnt_out                           false
% 2.84/1.02  --trig_cnt_out                          false
% 2.84/1.02  --trig_cnt_out_tolerance                1.
% 2.84/1.02  --trig_cnt_out_sk_spl                   false
% 2.84/1.02  --abstr_cl_out                          false
% 2.84/1.02  
% 2.84/1.02  ------ Global Options
% 2.84/1.02  
% 2.84/1.02  --schedule                              default
% 2.84/1.02  --add_important_lit                     false
% 2.84/1.02  --prop_solver_per_cl                    1000
% 2.84/1.02  --min_unsat_core                        false
% 2.84/1.02  --soft_assumptions                      false
% 2.84/1.02  --soft_lemma_size                       3
% 2.84/1.02  --prop_impl_unit_size                   0
% 2.84/1.02  --prop_impl_unit                        []
% 2.84/1.02  --share_sel_clauses                     true
% 2.84/1.02  --reset_solvers                         false
% 2.84/1.02  --bc_imp_inh                            [conj_cone]
% 2.84/1.02  --conj_cone_tolerance                   3.
% 2.84/1.02  --extra_neg_conj                        none
% 2.84/1.02  --large_theory_mode                     true
% 2.84/1.02  --prolific_symb_bound                   200
% 2.84/1.02  --lt_threshold                          2000
% 2.84/1.02  --clause_weak_htbl                      true
% 2.84/1.02  --gc_record_bc_elim                     false
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing Options
% 2.84/1.02  
% 2.84/1.02  --preprocessing_flag                    true
% 2.84/1.02  --time_out_prep_mult                    0.1
% 2.84/1.02  --splitting_mode                        input
% 2.84/1.02  --splitting_grd                         true
% 2.84/1.02  --splitting_cvd                         false
% 2.84/1.02  --splitting_cvd_svl                     false
% 2.84/1.02  --splitting_nvd                         32
% 2.84/1.02  --sub_typing                            true
% 2.84/1.02  --prep_gs_sim                           true
% 2.84/1.02  --prep_unflatten                        true
% 2.84/1.02  --prep_res_sim                          true
% 2.84/1.02  --prep_upred                            true
% 2.84/1.02  --prep_sem_filter                       exhaustive
% 2.84/1.02  --prep_sem_filter_out                   false
% 2.84/1.02  --pred_elim                             true
% 2.84/1.02  --res_sim_input                         true
% 2.84/1.02  --eq_ax_congr_red                       true
% 2.84/1.02  --pure_diseq_elim                       true
% 2.84/1.02  --brand_transform                       false
% 2.84/1.02  --non_eq_to_eq                          false
% 2.84/1.02  --prep_def_merge                        true
% 2.84/1.02  --prep_def_merge_prop_impl              false
% 2.84/1.02  --prep_def_merge_mbd                    true
% 2.84/1.02  --prep_def_merge_tr_red                 false
% 2.84/1.02  --prep_def_merge_tr_cl                  false
% 2.84/1.02  --smt_preprocessing                     true
% 2.84/1.02  --smt_ac_axioms                         fast
% 2.84/1.02  --preprocessed_out                      false
% 2.84/1.02  --preprocessed_stats                    false
% 2.84/1.02  
% 2.84/1.02  ------ Abstraction refinement Options
% 2.84/1.02  
% 2.84/1.02  --abstr_ref                             []
% 2.84/1.02  --abstr_ref_prep                        false
% 2.84/1.02  --abstr_ref_until_sat                   false
% 2.84/1.02  --abstr_ref_sig_restrict                funpre
% 2.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.02  --abstr_ref_under                       []
% 2.84/1.02  
% 2.84/1.02  ------ SAT Options
% 2.84/1.02  
% 2.84/1.02  --sat_mode                              false
% 2.84/1.02  --sat_fm_restart_options                ""
% 2.84/1.02  --sat_gr_def                            false
% 2.84/1.02  --sat_epr_types                         true
% 2.84/1.02  --sat_non_cyclic_types                  false
% 2.84/1.02  --sat_finite_models                     false
% 2.84/1.02  --sat_fm_lemmas                         false
% 2.84/1.02  --sat_fm_prep                           false
% 2.84/1.02  --sat_fm_uc_incr                        true
% 2.84/1.02  --sat_out_model                         small
% 2.84/1.02  --sat_out_clauses                       false
% 2.84/1.02  
% 2.84/1.02  ------ QBF Options
% 2.84/1.02  
% 2.84/1.02  --qbf_mode                              false
% 2.84/1.02  --qbf_elim_univ                         false
% 2.84/1.02  --qbf_dom_inst                          none
% 2.84/1.02  --qbf_dom_pre_inst                      false
% 2.84/1.02  --qbf_sk_in                             false
% 2.84/1.02  --qbf_pred_elim                         true
% 2.84/1.02  --qbf_split                             512
% 2.84/1.02  
% 2.84/1.02  ------ BMC1 Options
% 2.84/1.02  
% 2.84/1.02  --bmc1_incremental                      false
% 2.84/1.02  --bmc1_axioms                           reachable_all
% 2.84/1.02  --bmc1_min_bound                        0
% 2.84/1.02  --bmc1_max_bound                        -1
% 2.84/1.02  --bmc1_max_bound_default                -1
% 2.84/1.02  --bmc1_symbol_reachability              true
% 2.84/1.02  --bmc1_property_lemmas                  false
% 2.84/1.02  --bmc1_k_induction                      false
% 2.84/1.02  --bmc1_non_equiv_states                 false
% 2.84/1.02  --bmc1_deadlock                         false
% 2.84/1.02  --bmc1_ucm                              false
% 2.84/1.02  --bmc1_add_unsat_core                   none
% 2.84/1.02  --bmc1_unsat_core_children              false
% 2.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.02  --bmc1_out_stat                         full
% 2.84/1.02  --bmc1_ground_init                      false
% 2.84/1.02  --bmc1_pre_inst_next_state              false
% 2.84/1.02  --bmc1_pre_inst_state                   false
% 2.84/1.02  --bmc1_pre_inst_reach_state             false
% 2.84/1.02  --bmc1_out_unsat_core                   false
% 2.84/1.02  --bmc1_aig_witness_out                  false
% 2.84/1.02  --bmc1_verbose                          false
% 2.84/1.02  --bmc1_dump_clauses_tptp                false
% 2.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.02  --bmc1_dump_file                        -
% 2.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.02  --bmc1_ucm_extend_mode                  1
% 2.84/1.02  --bmc1_ucm_init_mode                    2
% 2.84/1.02  --bmc1_ucm_cone_mode                    none
% 2.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.02  --bmc1_ucm_relax_model                  4
% 2.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.02  --bmc1_ucm_layered_model                none
% 2.84/1.02  --bmc1_ucm_max_lemma_size               10
% 2.84/1.02  
% 2.84/1.02  ------ AIG Options
% 2.84/1.02  
% 2.84/1.02  --aig_mode                              false
% 2.84/1.02  
% 2.84/1.02  ------ Instantiation Options
% 2.84/1.02  
% 2.84/1.02  --instantiation_flag                    true
% 2.84/1.02  --inst_sos_flag                         false
% 2.84/1.02  --inst_sos_phase                        true
% 2.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.02  --inst_lit_sel_side                     none
% 2.84/1.02  --inst_solver_per_active                1400
% 2.84/1.02  --inst_solver_calls_frac                1.
% 2.84/1.02  --inst_passive_queue_type               priority_queues
% 2.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.02  --inst_passive_queues_freq              [25;2]
% 2.84/1.02  --inst_dismatching                      true
% 2.84/1.02  --inst_eager_unprocessed_to_passive     true
% 2.84/1.02  --inst_prop_sim_given                   true
% 2.84/1.02  --inst_prop_sim_new                     false
% 2.84/1.02  --inst_subs_new                         false
% 2.84/1.02  --inst_eq_res_simp                      false
% 2.84/1.02  --inst_subs_given                       false
% 2.84/1.02  --inst_orphan_elimination               true
% 2.84/1.02  --inst_learning_loop_flag               true
% 2.84/1.02  --inst_learning_start                   3000
% 2.84/1.02  --inst_learning_factor                  2
% 2.84/1.02  --inst_start_prop_sim_after_learn       3
% 2.84/1.02  --inst_sel_renew                        solver
% 2.84/1.02  --inst_lit_activity_flag                true
% 2.84/1.02  --inst_restr_to_given                   false
% 2.84/1.02  --inst_activity_threshold               500
% 2.84/1.02  --inst_out_proof                        true
% 2.84/1.02  
% 2.84/1.02  ------ Resolution Options
% 2.84/1.02  
% 2.84/1.02  --resolution_flag                       false
% 2.84/1.02  --res_lit_sel                           adaptive
% 2.84/1.02  --res_lit_sel_side                      none
% 2.84/1.02  --res_ordering                          kbo
% 2.84/1.02  --res_to_prop_solver                    active
% 2.84/1.02  --res_prop_simpl_new                    false
% 2.84/1.02  --res_prop_simpl_given                  true
% 2.84/1.02  --res_passive_queue_type                priority_queues
% 2.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.02  --res_passive_queues_freq               [15;5]
% 2.84/1.02  --res_forward_subs                      full
% 2.84/1.02  --res_backward_subs                     full
% 2.84/1.02  --res_forward_subs_resolution           true
% 2.84/1.02  --res_backward_subs_resolution          true
% 2.84/1.02  --res_orphan_elimination                true
% 2.84/1.02  --res_time_limit                        2.
% 2.84/1.02  --res_out_proof                         true
% 2.84/1.02  
% 2.84/1.02  ------ Superposition Options
% 2.84/1.02  
% 2.84/1.02  --superposition_flag                    true
% 2.84/1.02  --sup_passive_queue_type                priority_queues
% 2.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.02  --demod_completeness_check              fast
% 2.84/1.02  --demod_use_ground                      true
% 2.84/1.02  --sup_to_prop_solver                    passive
% 2.84/1.02  --sup_prop_simpl_new                    true
% 2.84/1.02  --sup_prop_simpl_given                  true
% 2.84/1.02  --sup_fun_splitting                     false
% 2.84/1.02  --sup_smt_interval                      50000
% 2.84/1.02  
% 2.84/1.02  ------ Superposition Simplification Setup
% 2.84/1.02  
% 2.84/1.02  --sup_indices_passive                   []
% 2.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_full_bw                           [BwDemod]
% 2.84/1.02  --sup_immed_triv                        [TrivRules]
% 2.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_immed_bw_main                     []
% 2.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.02  
% 2.84/1.02  ------ Combination Options
% 2.84/1.02  
% 2.84/1.02  --comb_res_mult                         3
% 2.84/1.02  --comb_sup_mult                         2
% 2.84/1.02  --comb_inst_mult                        10
% 2.84/1.02  
% 2.84/1.02  ------ Debug Options
% 2.84/1.02  
% 2.84/1.02  --dbg_backtrace                         false
% 2.84/1.02  --dbg_dump_prop_clauses                 false
% 2.84/1.02  --dbg_dump_prop_clauses_file            -
% 2.84/1.02  --dbg_out_stat                          false
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  ------ Proving...
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  % SZS status Theorem for theBenchmark.p
% 2.84/1.02  
% 2.84/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/1.02  
% 2.84/1.02  fof(f8,axiom,(
% 2.84/1.02    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f35,plain,(
% 2.84/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.84/1.02    inference(nnf_transformation,[],[f8])).
% 2.84/1.02  
% 2.84/1.02  fof(f36,plain,(
% 2.84/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.84/1.02    inference(rectify,[],[f35])).
% 2.84/1.02  
% 2.84/1.02  fof(f39,plain,(
% 2.84/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f38,plain,(
% 2.84/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f37,plain,(
% 2.84/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f40,plain,(
% 2.84/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f36,f39,f38,f37])).
% 2.84/1.02  
% 2.84/1.02  fof(f63,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f40])).
% 2.84/1.02  
% 2.84/1.02  fof(f5,axiom,(
% 2.84/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f28,plain,(
% 2.84/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.02    inference(nnf_transformation,[],[f5])).
% 2.84/1.02  
% 2.84/1.02  fof(f29,plain,(
% 2.84/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.02    inference(flattening,[],[f28])).
% 2.84/1.02  
% 2.84/1.02  fof(f56,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.84/1.02    inference(cnf_transformation,[],[f29])).
% 2.84/1.02  
% 2.84/1.02  fof(f77,plain,(
% 2.84/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.84/1.02    inference(equality_resolution,[],[f56])).
% 2.84/1.02  
% 2.84/1.02  fof(f6,axiom,(
% 2.84/1.02    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f57,plain,(
% 2.84/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.84/1.02    inference(cnf_transformation,[],[f6])).
% 2.84/1.02  
% 2.84/1.02  fof(f9,axiom,(
% 2.84/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f66,plain,(
% 2.84/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.84/1.02    inference(cnf_transformation,[],[f9])).
% 2.84/1.02  
% 2.84/1.02  fof(f1,axiom,(
% 2.84/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f14,plain,(
% 2.84/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.84/1.02    inference(ennf_transformation,[],[f1])).
% 2.84/1.02  
% 2.84/1.02  fof(f20,plain,(
% 2.84/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.84/1.02    inference(nnf_transformation,[],[f14])).
% 2.84/1.02  
% 2.84/1.02  fof(f21,plain,(
% 2.84/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.84/1.02    inference(rectify,[],[f20])).
% 2.84/1.02  
% 2.84/1.02  fof(f22,plain,(
% 2.84/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f23,plain,(
% 2.84/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.84/1.02  
% 2.84/1.02  fof(f46,plain,(
% 2.84/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f23])).
% 2.84/1.02  
% 2.84/1.02  fof(f4,axiom,(
% 2.84/1.02    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f24,plain,(
% 2.84/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.84/1.02    inference(nnf_transformation,[],[f4])).
% 2.84/1.02  
% 2.84/1.02  fof(f25,plain,(
% 2.84/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.84/1.02    inference(rectify,[],[f24])).
% 2.84/1.02  
% 2.84/1.02  fof(f26,plain,(
% 2.84/1.02    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f27,plain,(
% 2.84/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 2.84/1.02  
% 2.84/1.02  fof(f50,plain,(
% 2.84/1.02    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.84/1.02    inference(cnf_transformation,[],[f27])).
% 2.84/1.02  
% 2.84/1.02  fof(f76,plain,(
% 2.84/1.02    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.84/1.02    inference(equality_resolution,[],[f50])).
% 2.84/1.02  
% 2.84/1.02  fof(f11,axiom,(
% 2.84/1.02    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f17,plain,(
% 2.84/1.02    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 2.84/1.02    inference(ennf_transformation,[],[f11])).
% 2.84/1.02  
% 2.84/1.02  fof(f41,plain,(
% 2.84/1.02    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK8(X0,X1)) & k1_relat_1(sK8(X0,X1)) = X0 & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1))))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f42,plain,(
% 2.84/1.02    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK8(X0,X1)) & k1_relat_1(sK8(X0,X1)) = X0 & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1))) | k1_xboole_0 = X0)),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f41])).
% 2.84/1.02  
% 2.84/1.02  fof(f71,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK8(X0,X1)) | k1_xboole_0 = X0) )),
% 2.84/1.02    inference(cnf_transformation,[],[f42])).
% 2.84/1.02  
% 2.84/1.02  fof(f70,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k1_relat_1(sK8(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 2.84/1.02    inference(cnf_transformation,[],[f42])).
% 2.84/1.02  
% 2.84/1.02  fof(f12,conjecture,(
% 2.84/1.02    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f13,negated_conjecture,(
% 2.84/1.02    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.84/1.02    inference(negated_conjecture,[],[f12])).
% 2.84/1.02  
% 2.84/1.02  fof(f18,plain,(
% 2.84/1.02    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.84/1.02    inference(ennf_transformation,[],[f13])).
% 2.84/1.02  
% 2.84/1.02  fof(f19,plain,(
% 2.84/1.02    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.84/1.02    inference(flattening,[],[f18])).
% 2.84/1.02  
% 2.84/1.02  fof(f43,plain,(
% 2.84/1.02    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK9) | k1_relat_1(X2) != sK10 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK10 | k1_xboole_0 != sK9))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f44,plain,(
% 2.84/1.02    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK9) | k1_relat_1(X2) != sK10 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK10 | k1_xboole_0 != sK9)),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f19,f43])).
% 2.84/1.02  
% 2.84/1.02  fof(f73,plain,(
% 2.84/1.02    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK9) | k1_relat_1(X2) != sK10 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f44])).
% 2.84/1.02  
% 2.84/1.02  fof(f68,plain,(
% 2.84/1.02    ( ! [X0,X1] : (v1_relat_1(sK8(X0,X1)) | k1_xboole_0 = X0) )),
% 2.84/1.02    inference(cnf_transformation,[],[f42])).
% 2.84/1.02  
% 2.84/1.02  fof(f69,plain,(
% 2.84/1.02    ( ! [X0,X1] : (v1_funct_1(sK8(X0,X1)) | k1_xboole_0 = X0) )),
% 2.84/1.02    inference(cnf_transformation,[],[f42])).
% 2.84/1.02  
% 2.84/1.02  fof(f65,plain,(
% 2.84/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.84/1.02    inference(cnf_transformation,[],[f9])).
% 2.84/1.02  
% 2.84/1.02  fof(f2,axiom,(
% 2.84/1.02    v1_xboole_0(k1_xboole_0)),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f48,plain,(
% 2.84/1.02    v1_xboole_0(k1_xboole_0)),
% 2.84/1.02    inference(cnf_transformation,[],[f2])).
% 2.84/1.02  
% 2.84/1.02  fof(f10,axiom,(
% 2.84/1.02    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f16,plain,(
% 2.84/1.02    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.84/1.02    inference(ennf_transformation,[],[f10])).
% 2.84/1.02  
% 2.84/1.02  fof(f67,plain,(
% 2.84/1.02    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f16])).
% 2.84/1.02  
% 2.84/1.02  fof(f3,axiom,(
% 2.84/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f49,plain,(
% 2.84/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f3])).
% 2.84/1.02  
% 2.84/1.02  fof(f7,axiom,(
% 2.84/1.02    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.02  
% 2.84/1.02  fof(f15,plain,(
% 2.84/1.02    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.84/1.02    inference(ennf_transformation,[],[f7])).
% 2.84/1.02  
% 2.84/1.02  fof(f30,plain,(
% 2.84/1.02    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 2.84/1.02    inference(nnf_transformation,[],[f15])).
% 2.84/1.02  
% 2.84/1.02  fof(f31,plain,(
% 2.84/1.02    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.84/1.02    inference(rectify,[],[f30])).
% 2.84/1.02  
% 2.84/1.02  fof(f33,plain,(
% 2.84/1.02    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK3(X4),sK4(X4)) = X4)),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f32,plain,(
% 2.84/1.02    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 2.84/1.02    introduced(choice_axiom,[])).
% 2.84/1.02  
% 2.84/1.02  fof(f34,plain,(
% 2.84/1.02    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0))) & (! [X4] : (k4_tarski(sK3(X4),sK4(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f33,f32])).
% 2.84/1.02  
% 2.84/1.02  fof(f59,plain,(
% 2.84/1.02    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f34])).
% 2.84/1.02  
% 2.84/1.02  fof(f47,plain,(
% 2.84/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f23])).
% 2.84/1.02  
% 2.84/1.02  fof(f51,plain,(
% 2.84/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.84/1.02    inference(cnf_transformation,[],[f27])).
% 2.84/1.02  
% 2.84/1.02  fof(f74,plain,(
% 2.84/1.02    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.84/1.02    inference(equality_resolution,[],[f51])).
% 2.84/1.02  
% 2.84/1.02  fof(f75,plain,(
% 2.84/1.02    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.84/1.02    inference(equality_resolution,[],[f74])).
% 2.84/1.02  
% 2.84/1.02  fof(f55,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.84/1.02    inference(cnf_transformation,[],[f29])).
% 2.84/1.02  
% 2.84/1.02  fof(f78,plain,(
% 2.84/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.84/1.02    inference(equality_resolution,[],[f55])).
% 2.84/1.02  
% 2.84/1.02  fof(f54,plain,(
% 2.84/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.84/1.02    inference(cnf_transformation,[],[f29])).
% 2.84/1.02  
% 2.84/1.02  fof(f72,plain,(
% 2.84/1.02    k1_xboole_0 = sK10 | k1_xboole_0 != sK9),
% 2.84/1.02    inference(cnf_transformation,[],[f44])).
% 2.84/1.02  
% 2.84/1.02  cnf(c_17,plain,
% 2.84/1.02      ( r2_hidden(sK5(X0,X1),X1)
% 2.84/1.02      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
% 2.84/1.02      | k2_relat_1(X0) = X1 ),
% 2.84/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1293,plain,
% 2.84/1.02      ( k2_relat_1(X0) = X1
% 2.84/1.02      | r2_hidden(sK5(X0,X1),X1) = iProver_top
% 2.84/1.02      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_9,plain,
% 2.84/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_12,plain,
% 2.84/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.84/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1298,plain,
% 2.84/1.02      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_2014,plain,
% 2.84/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_9,c_1298]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_3371,plain,
% 2.84/1.02      ( k2_relat_1(k1_xboole_0) = X0
% 2.84/1.02      | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_1293,c_2014]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_20,plain,
% 2.84/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_3374,plain,
% 2.84/1.02      ( k1_xboole_0 = X0
% 2.84/1.02      | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 2.84/1.02      inference(demodulation,[status(thm)],[c_3371,c_20]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1,plain,
% 2.84/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.84/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1305,plain,
% 2.84/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.84/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_8,plain,
% 2.84/1.02      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.84/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1299,plain,
% 2.84/1.02      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_2266,plain,
% 2.84/1.02      ( sK0(k1_tarski(X0),X1) = X0
% 2.84/1.02      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_1305,c_1299]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_23,plain,
% 2.84/1.02      ( k2_relat_1(sK8(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_24,plain,
% 2.84/1.02      ( k1_relat_1(sK8(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_27,negated_conjecture,
% 2.84/1.02      ( ~ r1_tarski(k2_relat_1(X0),sK9)
% 2.84/1.02      | ~ v1_funct_1(X0)
% 2.84/1.02      | ~ v1_relat_1(X0)
% 2.84/1.02      | k1_relat_1(X0) != sK10 ),
% 2.84/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1288,plain,
% 2.84/1.02      ( k1_relat_1(X0) != sK10
% 2.84/1.02      | r1_tarski(k2_relat_1(X0),sK9) != iProver_top
% 2.84/1.02      | v1_funct_1(X0) != iProver_top
% 2.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1561,plain,
% 2.84/1.02      ( sK10 != X0
% 2.84/1.02      | k1_xboole_0 = X0
% 2.84/1.02      | r1_tarski(k2_relat_1(sK8(X0,X1)),sK9) != iProver_top
% 2.84/1.02      | v1_funct_1(sK8(X0,X1)) != iProver_top
% 2.84/1.02      | v1_relat_1(sK8(X0,X1)) != iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_24,c_1288]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_26,plain,
% 2.84/1.02      ( v1_relat_1(sK8(X0,X1)) | k1_xboole_0 = X0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_32,plain,
% 2.84/1.02      ( k1_xboole_0 = X0 | v1_relat_1(sK8(X0,X1)) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_25,plain,
% 2.84/1.02      ( v1_funct_1(sK8(X0,X1)) | k1_xboole_0 = X0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_35,plain,
% 2.84/1.02      ( k1_xboole_0 = X0 | v1_funct_1(sK8(X0,X1)) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1782,plain,
% 2.84/1.02      ( sK10 != X0
% 2.84/1.02      | k1_xboole_0 = X0
% 2.84/1.02      | r1_tarski(k2_relat_1(sK8(X0,X1)),sK9) != iProver_top ),
% 2.84/1.02      inference(global_propositional_subsumption,
% 2.84/1.02                [status(thm)],
% 2.84/1.02                [c_1561,c_32,c_35]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1789,plain,
% 2.84/1.02      ( sK10 = k1_xboole_0
% 2.84/1.02      | r1_tarski(k2_relat_1(sK8(sK10,X0)),sK9) != iProver_top ),
% 2.84/1.02      inference(equality_resolution,[status(thm)],[c_1782]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1923,plain,
% 2.84/1.02      ( sK10 = k1_xboole_0
% 2.84/1.02      | r1_tarski(k1_tarski(X0),sK9) != iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_23,c_1789]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_5765,plain,
% 2.84/1.02      ( sK0(k1_tarski(X0),sK9) = X0 | sK10 = k1_xboole_0 ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_2266,c_1923]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_21,plain,
% 2.84/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_3,plain,
% 2.84/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.84/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_22,plain,
% 2.84/1.02      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.84/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_253,plain,
% 2.84/1.02      ( v1_funct_1(X0) | k1_xboole_0 != X0 ),
% 2.84/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_254,plain,
% 2.84/1.02      ( v1_funct_1(k1_xboole_0) ),
% 2.84/1.02      inference(unflattening,[status(thm)],[c_253]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_687,plain,
% 2.84/1.02      ( ~ r1_tarski(k2_relat_1(X0),sK9)
% 2.84/1.02      | ~ v1_relat_1(X0)
% 2.84/1.02      | k1_relat_1(X0) != sK10
% 2.84/1.02      | k1_xboole_0 != X0 ),
% 2.84/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_254]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_688,plain,
% 2.84/1.02      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK9)
% 2.84/1.02      | ~ v1_relat_1(k1_xboole_0)
% 2.84/1.02      | k1_relat_1(k1_xboole_0) != sK10 ),
% 2.84/1.02      inference(unflattening,[status(thm)],[c_687]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_41,plain,
% 2.84/1.02      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_22]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_4,plain,
% 2.84/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.84/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_374,plain,
% 2.84/1.02      ( ~ v1_funct_1(X0)
% 2.84/1.02      | ~ v1_relat_1(X0)
% 2.84/1.02      | k1_relat_1(X0) != sK10
% 2.84/1.02      | k2_relat_1(X0) != k1_xboole_0
% 2.84/1.02      | sK9 != X1 ),
% 2.84/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_375,plain,
% 2.84/1.02      ( ~ v1_funct_1(X0)
% 2.84/1.02      | ~ v1_relat_1(X0)
% 2.84/1.02      | k1_relat_1(X0) != sK10
% 2.84/1.02      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.84/1.02      inference(unflattening,[status(thm)],[c_374]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_377,plain,
% 2.84/1.02      ( ~ v1_funct_1(k1_xboole_0)
% 2.84/1.02      | ~ v1_relat_1(k1_xboole_0)
% 2.84/1.02      | k1_relat_1(k1_xboole_0) != sK10
% 2.84/1.02      | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_375]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_690,plain,
% 2.84/1.02      ( ~ v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK10 ),
% 2.84/1.02      inference(global_propositional_subsumption,
% 2.84/1.02                [status(thm)],
% 2.84/1.02                [c_688,c_41,c_20,c_3,c_377]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_692,plain,
% 2.84/1.02      ( k1_relat_1(k1_xboole_0) != sK10
% 2.84/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_918,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1549,plain,
% 2.84/1.02      ( k1_relat_1(X0) != X1 | k1_relat_1(X0) = sK10 | sK10 != X1 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_918]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1550,plain,
% 2.84/1.02      ( k1_relat_1(k1_xboole_0) = sK10
% 2.84/1.02      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.84/1.02      | sK10 != k1_xboole_0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_1549]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_14,plain,
% 2.84/1.02      ( r2_hidden(sK2(X0),X0) | v1_relat_1(X0) ),
% 2.84/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1296,plain,
% 2.84/1.02      ( r2_hidden(sK2(X0),X0) = iProver_top
% 2.84/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_2224,plain,
% 2.84/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_1296,c_2014]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_6490,plain,
% 2.84/1.02      ( sK0(k1_tarski(X0),sK9) = X0 ),
% 2.84/1.02      inference(global_propositional_subsumption,
% 2.84/1.02                [status(thm)],
% 2.84/1.02                [c_5765,c_21,c_692,c_1550,c_2224]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_0,plain,
% 2.84/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.84/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1306,plain,
% 2.84/1.02      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.84/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.84/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_6494,plain,
% 2.84/1.02      ( r2_hidden(X0,sK9) != iProver_top
% 2.84/1.02      | r1_tarski(k1_tarski(X0),sK9) = iProver_top ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_6490,c_1306]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_6504,plain,
% 2.84/1.02      ( r2_hidden(X0,sK9) != iProver_top ),
% 2.84/1.02      inference(global_propositional_subsumption,
% 2.84/1.02                [status(thm)],
% 2.84/1.02                [c_6494,c_21,c_692,c_1550,c_1923,c_2224]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_6516,plain,
% 2.84/1.02      ( sK9 = k1_xboole_0 ),
% 2.84/1.02      inference(superposition,[status(thm)],[c_3374,c_6504]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1690,plain,
% 2.84/1.02      ( X0 != X1 | sK10 != X1 | sK10 = X0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_918]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_2025,plain,
% 2.84/1.02      ( X0 != sK10 | sK10 = X0 | sK10 != sK10 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_1690]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_2027,plain,
% 2.84/1.02      ( sK10 != sK10 | sK10 = k1_xboole_0 | k1_xboole_0 != sK10 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_2025]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_7,plain,
% 2.84/1.02      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.84/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1998,plain,
% 2.84/1.02      ( r2_hidden(sK10,k1_tarski(sK10)) ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1691,plain,
% 2.84/1.02      ( ~ r2_hidden(sK10,k1_tarski(X0)) | sK10 = X0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1997,plain,
% 2.84/1.02      ( ~ r2_hidden(sK10,k1_tarski(sK10)) | sK10 = sK10 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_1691]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1525,plain,
% 2.84/1.02      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_918]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_1526,plain,
% 2.84/1.02      ( sK9 != k1_xboole_0
% 2.84/1.02      | k1_xboole_0 = sK9
% 2.84/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_1525]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_10,plain,
% 2.84/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_64,plain,
% 2.84/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_11,plain,
% 2.84/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.84/1.02      | k1_xboole_0 = X1
% 2.84/1.02      | k1_xboole_0 = X0 ),
% 2.84/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_63,plain,
% 2.84/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.84/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 2.84/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(c_28,negated_conjecture,
% 2.84/1.02      ( k1_xboole_0 = sK10 | k1_xboole_0 != sK9 ),
% 2.84/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.84/1.02  
% 2.84/1.02  cnf(contradiction,plain,
% 2.84/1.02      ( $false ),
% 2.84/1.02      inference(minisat,
% 2.84/1.02                [status(thm)],
% 2.84/1.02                [c_6516,c_2224,c_2027,c_1998,c_1997,c_1550,c_1526,c_692,
% 2.84/1.02                 c_64,c_63,c_21,c_28]) ).
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/1.02  
% 2.84/1.02  ------                               Statistics
% 2.84/1.02  
% 2.84/1.02  ------ General
% 2.84/1.02  
% 2.84/1.02  abstr_ref_over_cycles:                  0
% 2.84/1.02  abstr_ref_under_cycles:                 0
% 2.84/1.02  gc_basic_clause_elim:                   0
% 2.84/1.02  forced_gc_time:                         0
% 2.84/1.02  parsing_time:                           0.014
% 2.84/1.02  unif_index_cands_time:                  0.
% 2.84/1.02  unif_index_add_time:                    0.
% 2.84/1.02  orderings_time:                         0.
% 2.84/1.02  out_proof_time:                         0.013
% 2.84/1.02  total_time:                             0.232
% 2.84/1.02  num_of_symbols:                         53
% 2.84/1.02  num_of_terms:                           8695
% 2.84/1.02  
% 2.84/1.02  ------ Preprocessing
% 2.84/1.02  
% 2.84/1.02  num_of_splits:                          0
% 2.84/1.02  num_of_split_atoms:                     0
% 2.84/1.02  num_of_reused_defs:                     0
% 2.84/1.02  num_eq_ax_congr_red:                    48
% 2.84/1.02  num_of_sem_filtered_clauses:            1
% 2.84/1.02  num_of_subtypes:                        0
% 2.84/1.02  monotx_restored_types:                  0
% 2.84/1.02  sat_num_of_epr_types:                   0
% 2.84/1.02  sat_num_of_non_cyclic_types:            0
% 2.84/1.02  sat_guarded_non_collapsed_types:        0
% 2.84/1.02  num_pure_diseq_elim:                    0
% 2.84/1.02  simp_replaced_by:                       0
% 2.84/1.02  res_preprocessed:                       134
% 2.84/1.02  prep_upred:                             0
% 2.84/1.02  prep_unflattend:                        35
% 2.84/1.02  smt_new_axioms:                         0
% 2.84/1.02  pred_elim_cands:                        4
% 2.84/1.02  pred_elim:                              1
% 2.84/1.02  pred_elim_cl:                           1
% 2.84/1.02  pred_elim_cycles:                       7
% 2.84/1.02  merged_defs:                            0
% 2.84/1.02  merged_defs_ncl:                        0
% 2.84/1.02  bin_hyper_res:                          0
% 2.84/1.02  prep_cycles:                            4
% 2.84/1.02  pred_elim_time:                         0.008
% 2.84/1.02  splitting_time:                         0.
% 2.84/1.02  sem_filter_time:                        0.
% 2.84/1.02  monotx_time:                            0.
% 2.84/1.02  subtype_inf_time:                       0.
% 2.84/1.02  
% 2.84/1.02  ------ Problem properties
% 2.84/1.02  
% 2.84/1.02  clauses:                                28
% 2.84/1.02  conjectures:                            2
% 2.84/1.02  epr:                                    4
% 2.84/1.02  horn:                                   19
% 2.84/1.02  ground:                                 4
% 2.84/1.02  unary:                                  8
% 2.84/1.02  binary:                                 12
% 2.84/1.02  lits:                                   57
% 2.84/1.02  lits_eq:                                25
% 2.84/1.02  fd_pure:                                0
% 2.84/1.02  fd_pseudo:                              0
% 2.84/1.02  fd_cond:                                4
% 2.84/1.02  fd_pseudo_cond:                         4
% 2.84/1.02  ac_symbols:                             0
% 2.84/1.02  
% 2.84/1.02  ------ Propositional Solver
% 2.84/1.02  
% 2.84/1.02  prop_solver_calls:                      28
% 2.84/1.02  prop_fast_solver_calls:                 825
% 2.84/1.02  smt_solver_calls:                       0
% 2.84/1.02  smt_fast_solver_calls:                  0
% 2.84/1.02  prop_num_of_clauses:                    2525
% 2.84/1.02  prop_preprocess_simplified:             8195
% 2.84/1.02  prop_fo_subsumed:                       10
% 2.84/1.02  prop_solver_time:                       0.
% 2.84/1.02  smt_solver_time:                        0.
% 2.84/1.02  smt_fast_solver_time:                   0.
% 2.84/1.02  prop_fast_solver_time:                  0.
% 2.84/1.02  prop_unsat_core_time:                   0.
% 2.84/1.02  
% 2.84/1.02  ------ QBF
% 2.84/1.02  
% 2.84/1.02  qbf_q_res:                              0
% 2.84/1.02  qbf_num_tautologies:                    0
% 2.84/1.02  qbf_prep_cycles:                        0
% 2.84/1.02  
% 2.84/1.02  ------ BMC1
% 2.84/1.02  
% 2.84/1.02  bmc1_current_bound:                     -1
% 2.84/1.02  bmc1_last_solved_bound:                 -1
% 2.84/1.02  bmc1_unsat_core_size:                   -1
% 2.84/1.02  bmc1_unsat_core_parents_size:           -1
% 2.84/1.02  bmc1_merge_next_fun:                    0
% 2.84/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.84/1.02  
% 2.84/1.02  ------ Instantiation
% 2.84/1.02  
% 2.84/1.02  inst_num_of_clauses:                    650
% 2.84/1.02  inst_num_in_passive:                    387
% 2.84/1.02  inst_num_in_active:                     261
% 2.84/1.02  inst_num_in_unprocessed:                2
% 2.84/1.02  inst_num_of_loops:                      320
% 2.84/1.02  inst_num_of_learning_restarts:          0
% 2.84/1.02  inst_num_moves_active_passive:          57
% 2.84/1.02  inst_lit_activity:                      0
% 2.84/1.02  inst_lit_activity_moves:                0
% 2.84/1.02  inst_num_tautologies:                   0
% 2.84/1.02  inst_num_prop_implied:                  0
% 2.84/1.02  inst_num_existing_simplified:           0
% 2.84/1.02  inst_num_eq_res_simplified:             0
% 2.84/1.02  inst_num_child_elim:                    0
% 2.84/1.02  inst_num_of_dismatching_blockings:      386
% 2.84/1.02  inst_num_of_non_proper_insts:           567
% 2.84/1.02  inst_num_of_duplicates:                 0
% 2.84/1.02  inst_inst_num_from_inst_to_res:         0
% 2.84/1.02  inst_dismatching_checking_time:         0.
% 2.84/1.02  
% 2.84/1.02  ------ Resolution
% 2.84/1.02  
% 2.84/1.02  res_num_of_clauses:                     0
% 2.84/1.02  res_num_in_passive:                     0
% 2.84/1.02  res_num_in_active:                      0
% 2.84/1.02  res_num_of_loops:                       138
% 2.84/1.02  res_forward_subset_subsumed:            26
% 2.84/1.02  res_backward_subset_subsumed:           0
% 2.84/1.02  res_forward_subsumed:                   0
% 2.84/1.02  res_backward_subsumed:                  0
% 2.84/1.02  res_forward_subsumption_resolution:     0
% 2.84/1.02  res_backward_subsumption_resolution:    0
% 2.84/1.02  res_clause_to_clause_subsumption:       226
% 2.84/1.02  res_orphan_elimination:                 0
% 2.84/1.02  res_tautology_del:                      27
% 2.84/1.02  res_num_eq_res_simplified:              0
% 2.84/1.02  res_num_sel_changes:                    0
% 2.84/1.02  res_moves_from_active_to_pass:          0
% 2.84/1.02  
% 2.84/1.02  ------ Superposition
% 2.84/1.02  
% 2.84/1.02  sup_time_total:                         0.
% 2.84/1.02  sup_time_generating:                    0.
% 2.84/1.02  sup_time_sim_full:                      0.
% 2.84/1.02  sup_time_sim_immed:                     0.
% 2.84/1.02  
% 2.84/1.02  sup_num_of_clauses:                     114
% 2.84/1.02  sup_num_in_active:                      64
% 2.84/1.02  sup_num_in_passive:                     50
% 2.84/1.02  sup_num_of_loops:                       63
% 2.84/1.02  sup_fw_superposition:                   90
% 2.84/1.02  sup_bw_superposition:                   57
% 2.84/1.02  sup_immediate_simplified:               15
% 2.84/1.02  sup_given_eliminated:                   1
% 2.84/1.02  comparisons_done:                       0
% 2.84/1.02  comparisons_avoided:                    8
% 2.84/1.02  
% 2.84/1.02  ------ Simplifications
% 2.84/1.02  
% 2.84/1.02  
% 2.84/1.02  sim_fw_subset_subsumed:                 4
% 2.84/1.02  sim_bw_subset_subsumed:                 0
% 2.84/1.02  sim_fw_subsumed:                        6
% 2.84/1.02  sim_bw_subsumed:                        1
% 2.84/1.02  sim_fw_subsumption_res:                 1
% 2.84/1.02  sim_bw_subsumption_res:                 0
% 2.84/1.02  sim_tautology_del:                      3
% 2.84/1.02  sim_eq_tautology_del:                   4
% 2.84/1.02  sim_eq_res_simp:                        0
% 2.84/1.02  sim_fw_demodulated:                     2
% 2.84/1.02  sim_bw_demodulated:                     2
% 2.84/1.02  sim_light_normalised:                   5
% 2.84/1.02  sim_joinable_taut:                      0
% 2.84/1.02  sim_joinable_simp:                      0
% 2.84/1.02  sim_ac_normalised:                      0
% 2.84/1.02  sim_smt_subsumption:                    0
% 2.84/1.02  
%------------------------------------------------------------------------------
