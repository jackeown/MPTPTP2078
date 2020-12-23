%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:23 EST 2020

% Result     : Theorem 6.81s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :  136 (2684 expanded)
%              Number of clauses        :   75 ( 889 expanded)
%              Number of leaves         :   18 ( 682 expanded)
%              Depth                    :   26
%              Number of atoms          :  436 (12878 expanded)
%              Number of equality atoms :  257 (6405 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK6(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK6(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f39])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f37])).

fof(f61,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

fof(f11,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK7
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK7
              | k1_relat_1(X1) != sK7
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_xboole_0 != sK7
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK7
            | k1_relat_1(X1) != sK7
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f41])).

fof(f67,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK7
      | k1_relat_1(X1) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK5(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,plain,
    ( k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK7
    | k1_relat_1(X1) != sK7 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_608,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK7
    | k1_relat_1(X1) != sK7
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1053,plain,
    ( sK5(X0,X1) = X2
    | k1_relat_1(X2) != sK7
    | sK7 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_608])).

cnf(c_19,plain,
    ( v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_42,plain,
    ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1169,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK5(X0,X1) = X2
    | k1_relat_1(X2) != sK7
    | sK7 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_39,c_42])).

cnf(c_1170,plain,
    ( sK5(X0,X1) = X2
    | k1_relat_1(X2) != sK7
    | sK7 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1169])).

cnf(c_1181,plain,
    ( sK5(X0,X1) = sK6(X2)
    | sK7 != X2
    | sK7 != X0
    | v1_funct_1(sK6(X2)) != iProver_top
    | v1_relat_1(sK6(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1170])).

cnf(c_836,plain,
    ( sK6(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_608])).

cnf(c_23,plain,
    ( v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v1_relat_1(sK6(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK6(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_855,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK6(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_29,c_32])).

cnf(c_856,plain,
    ( sK6(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_855])).

cnf(c_1052,plain,
    ( sK5(X0,X1) = sK6(X2)
    | sK7 != X0
    | sK7 != X2
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_856])).

cnf(c_1078,plain,
    ( ~ v1_funct_1(sK5(X0,X1))
    | ~ v1_relat_1(sK5(X0,X1))
    | sK5(X0,X1) = sK6(X2)
    | sK7 != X0
    | sK7 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1052])).

cnf(c_1232,plain,
    ( sK5(X0,X1) = sK6(X2)
    | sK7 != X2
    | sK7 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_19,c_18,c_1078])).

cnf(c_1233,plain,
    ( sK5(X0,X1) = sK6(X2)
    | sK7 != X0
    | sK7 != X2 ),
    inference(renaming,[status(thm)],[c_1232])).

cnf(c_1238,plain,
    ( sK5(sK7,X0) = sK6(X1)
    | sK7 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1233])).

cnf(c_1273,plain,
    ( sK5(sK7,X0) = sK6(sK7) ),
    inference(equality_resolution,[status(thm)],[c_1238])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_620,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_619,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2898,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_619])).

cnf(c_10436,plain,
    ( k1_relat_1(sK5(X0,X1)) = X2
    | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK2(sK5(X0,X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2898])).

cnf(c_10656,plain,
    ( X0 = X1
    | r2_hidden(sK2(sK5(X1,X2),X0),X1) = iProver_top
    | r2_hidden(sK2(sK5(X1,X2),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10436,c_17])).

cnf(c_14555,plain,
    ( sK7 = X0
    | r2_hidden(sK2(sK5(sK7,X1),X0),X0) = iProver_top
    | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_10656])).

cnf(c_14921,plain,
    ( sK7 = X0
    | r2_hidden(sK2(sK6(sK7),X0),X0) = iProver_top
    | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14555,c_1273])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_622,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1475,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_622])).

cnf(c_15101,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_14921,c_1475])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_relat_1(sK6(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_73,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_81,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_245,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_826,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_827,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_615,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1917,plain,
    ( k2_relat_1(sK6(X0)) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_615])).

cnf(c_2244,plain,
    ( k1_xboole_0 != X0
    | k2_relat_1(sK6(X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1917,c_29])).

cnf(c_2245,plain,
    ( k2_relat_1(sK6(X0)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2244])).

cnf(c_2249,plain,
    ( k2_relat_1(sK6(k1_xboole_0)) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2245])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_617,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2355,plain,
    ( v1_relat_1(sK6(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK6(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_617])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_618,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_626,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2213,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_626])).

cnf(c_3665,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(sK6(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_2213])).

cnf(c_15091,plain,
    ( sK7 = X0
    | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top
    | v1_xboole_0(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14921,c_3665])).

cnf(c_15326,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top
    | v1_xboole_0(sK6(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15091])).

cnf(c_16026,plain,
    ( r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15101,c_24,c_31,c_73,c_74,c_81,c_827,c_2355,c_15326])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_614,plain,
    ( k1_funct_1(sK5(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_16038,plain,
    ( k1_funct_1(sK5(sK7,X0),sK2(sK6(sK7),k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_16026,c_614])).

cnf(c_16040,plain,
    ( k1_funct_1(sK6(sK7),sK2(sK6(sK7),k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_16038,c_1273])).

cnf(c_16166,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_16040,c_16040])).

cnf(c_17488,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_16166,c_24])).

cnf(c_17504,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17488,c_16166])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.81/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.81/1.50  
% 6.81/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.81/1.50  
% 6.81/1.50  ------  iProver source info
% 6.81/1.50  
% 6.81/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.81/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.81/1.50  git: non_committed_changes: false
% 6.81/1.50  git: last_make_outside_of_git: false
% 6.81/1.50  
% 6.81/1.50  ------ 
% 6.81/1.50  
% 6.81/1.50  ------ Input Options
% 6.81/1.50  
% 6.81/1.50  --out_options                           all
% 6.81/1.50  --tptp_safe_out                         true
% 6.81/1.50  --problem_path                          ""
% 6.81/1.50  --include_path                          ""
% 6.81/1.50  --clausifier                            res/vclausify_rel
% 6.81/1.50  --clausifier_options                    --mode clausify
% 6.81/1.50  --stdin                                 false
% 6.81/1.50  --stats_out                             all
% 6.81/1.50  
% 6.81/1.50  ------ General Options
% 6.81/1.50  
% 6.81/1.50  --fof                                   false
% 6.81/1.50  --time_out_real                         305.
% 6.81/1.50  --time_out_virtual                      -1.
% 6.81/1.50  --symbol_type_check                     false
% 6.81/1.50  --clausify_out                          false
% 6.81/1.50  --sig_cnt_out                           false
% 6.81/1.50  --trig_cnt_out                          false
% 6.81/1.50  --trig_cnt_out_tolerance                1.
% 6.81/1.50  --trig_cnt_out_sk_spl                   false
% 6.81/1.50  --abstr_cl_out                          false
% 6.81/1.50  
% 6.81/1.50  ------ Global Options
% 6.81/1.50  
% 6.81/1.50  --schedule                              default
% 6.81/1.50  --add_important_lit                     false
% 6.81/1.50  --prop_solver_per_cl                    1000
% 6.81/1.50  --min_unsat_core                        false
% 6.81/1.50  --soft_assumptions                      false
% 6.81/1.50  --soft_lemma_size                       3
% 6.81/1.50  --prop_impl_unit_size                   0
% 6.81/1.50  --prop_impl_unit                        []
% 6.81/1.50  --share_sel_clauses                     true
% 6.81/1.50  --reset_solvers                         false
% 6.81/1.50  --bc_imp_inh                            [conj_cone]
% 6.81/1.50  --conj_cone_tolerance                   3.
% 6.81/1.50  --extra_neg_conj                        none
% 6.81/1.50  --large_theory_mode                     true
% 6.81/1.50  --prolific_symb_bound                   200
% 6.81/1.50  --lt_threshold                          2000
% 6.81/1.50  --clause_weak_htbl                      true
% 6.81/1.50  --gc_record_bc_elim                     false
% 6.81/1.50  
% 6.81/1.50  ------ Preprocessing Options
% 6.81/1.50  
% 6.81/1.50  --preprocessing_flag                    true
% 6.81/1.50  --time_out_prep_mult                    0.1
% 6.81/1.50  --splitting_mode                        input
% 6.81/1.50  --splitting_grd                         true
% 6.81/1.50  --splitting_cvd                         false
% 6.81/1.50  --splitting_cvd_svl                     false
% 6.81/1.50  --splitting_nvd                         32
% 6.81/1.50  --sub_typing                            true
% 6.81/1.50  --prep_gs_sim                           true
% 6.81/1.50  --prep_unflatten                        true
% 6.81/1.50  --prep_res_sim                          true
% 6.81/1.50  --prep_upred                            true
% 6.81/1.50  --prep_sem_filter                       exhaustive
% 6.81/1.50  --prep_sem_filter_out                   false
% 6.81/1.50  --pred_elim                             true
% 6.81/1.50  --res_sim_input                         true
% 6.81/1.50  --eq_ax_congr_red                       true
% 6.81/1.50  --pure_diseq_elim                       true
% 6.81/1.50  --brand_transform                       false
% 6.81/1.50  --non_eq_to_eq                          false
% 6.81/1.50  --prep_def_merge                        true
% 6.81/1.50  --prep_def_merge_prop_impl              false
% 6.81/1.50  --prep_def_merge_mbd                    true
% 6.81/1.50  --prep_def_merge_tr_red                 false
% 6.81/1.50  --prep_def_merge_tr_cl                  false
% 6.81/1.50  --smt_preprocessing                     true
% 6.81/1.50  --smt_ac_axioms                         fast
% 6.81/1.50  --preprocessed_out                      false
% 6.81/1.50  --preprocessed_stats                    false
% 6.81/1.50  
% 6.81/1.50  ------ Abstraction refinement Options
% 6.81/1.50  
% 6.81/1.50  --abstr_ref                             []
% 6.81/1.50  --abstr_ref_prep                        false
% 6.81/1.50  --abstr_ref_until_sat                   false
% 6.81/1.50  --abstr_ref_sig_restrict                funpre
% 6.81/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.50  --abstr_ref_under                       []
% 6.81/1.50  
% 6.81/1.50  ------ SAT Options
% 6.81/1.50  
% 6.81/1.50  --sat_mode                              false
% 6.81/1.50  --sat_fm_restart_options                ""
% 6.81/1.50  --sat_gr_def                            false
% 6.81/1.50  --sat_epr_types                         true
% 6.81/1.50  --sat_non_cyclic_types                  false
% 6.81/1.50  --sat_finite_models                     false
% 6.81/1.50  --sat_fm_lemmas                         false
% 6.81/1.50  --sat_fm_prep                           false
% 6.81/1.50  --sat_fm_uc_incr                        true
% 6.81/1.50  --sat_out_model                         small
% 6.81/1.50  --sat_out_clauses                       false
% 6.81/1.50  
% 6.81/1.50  ------ QBF Options
% 6.81/1.50  
% 6.81/1.50  --qbf_mode                              false
% 6.81/1.50  --qbf_elim_univ                         false
% 6.81/1.50  --qbf_dom_inst                          none
% 6.81/1.50  --qbf_dom_pre_inst                      false
% 6.81/1.50  --qbf_sk_in                             false
% 6.81/1.50  --qbf_pred_elim                         true
% 6.81/1.50  --qbf_split                             512
% 6.81/1.50  
% 6.81/1.50  ------ BMC1 Options
% 6.81/1.50  
% 6.81/1.50  --bmc1_incremental                      false
% 6.81/1.50  --bmc1_axioms                           reachable_all
% 6.81/1.50  --bmc1_min_bound                        0
% 6.81/1.50  --bmc1_max_bound                        -1
% 6.81/1.50  --bmc1_max_bound_default                -1
% 6.81/1.50  --bmc1_symbol_reachability              true
% 6.81/1.50  --bmc1_property_lemmas                  false
% 6.81/1.50  --bmc1_k_induction                      false
% 6.81/1.50  --bmc1_non_equiv_states                 false
% 6.81/1.50  --bmc1_deadlock                         false
% 6.81/1.50  --bmc1_ucm                              false
% 6.81/1.50  --bmc1_add_unsat_core                   none
% 6.81/1.50  --bmc1_unsat_core_children              false
% 6.81/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.50  --bmc1_out_stat                         full
% 6.81/1.50  --bmc1_ground_init                      false
% 6.81/1.50  --bmc1_pre_inst_next_state              false
% 6.81/1.50  --bmc1_pre_inst_state                   false
% 6.81/1.50  --bmc1_pre_inst_reach_state             false
% 6.81/1.50  --bmc1_out_unsat_core                   false
% 6.81/1.50  --bmc1_aig_witness_out                  false
% 6.81/1.50  --bmc1_verbose                          false
% 6.81/1.50  --bmc1_dump_clauses_tptp                false
% 6.81/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.50  --bmc1_dump_file                        -
% 6.81/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.50  --bmc1_ucm_extend_mode                  1
% 6.81/1.50  --bmc1_ucm_init_mode                    2
% 6.81/1.50  --bmc1_ucm_cone_mode                    none
% 6.81/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.50  --bmc1_ucm_relax_model                  4
% 6.81/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.50  --bmc1_ucm_layered_model                none
% 6.81/1.50  --bmc1_ucm_max_lemma_size               10
% 6.81/1.50  
% 6.81/1.50  ------ AIG Options
% 6.81/1.50  
% 6.81/1.50  --aig_mode                              false
% 6.81/1.50  
% 6.81/1.50  ------ Instantiation Options
% 6.81/1.50  
% 6.81/1.50  --instantiation_flag                    true
% 6.81/1.50  --inst_sos_flag                         false
% 6.81/1.50  --inst_sos_phase                        true
% 6.81/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.50  --inst_lit_sel_side                     num_symb
% 6.81/1.50  --inst_solver_per_active                1400
% 6.81/1.50  --inst_solver_calls_frac                1.
% 6.81/1.50  --inst_passive_queue_type               priority_queues
% 6.81/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.50  --inst_passive_queues_freq              [25;2]
% 6.81/1.50  --inst_dismatching                      true
% 6.81/1.50  --inst_eager_unprocessed_to_passive     true
% 6.81/1.50  --inst_prop_sim_given                   true
% 6.81/1.50  --inst_prop_sim_new                     false
% 6.81/1.50  --inst_subs_new                         false
% 6.81/1.50  --inst_eq_res_simp                      false
% 6.81/1.50  --inst_subs_given                       false
% 6.81/1.50  --inst_orphan_elimination               true
% 6.81/1.50  --inst_learning_loop_flag               true
% 6.81/1.50  --inst_learning_start                   3000
% 6.81/1.50  --inst_learning_factor                  2
% 6.81/1.50  --inst_start_prop_sim_after_learn       3
% 6.81/1.50  --inst_sel_renew                        solver
% 6.81/1.50  --inst_lit_activity_flag                true
% 6.81/1.50  --inst_restr_to_given                   false
% 6.81/1.50  --inst_activity_threshold               500
% 6.81/1.50  --inst_out_proof                        true
% 6.81/1.50  
% 6.81/1.50  ------ Resolution Options
% 6.81/1.50  
% 6.81/1.50  --resolution_flag                       true
% 6.81/1.50  --res_lit_sel                           adaptive
% 6.81/1.50  --res_lit_sel_side                      none
% 6.81/1.50  --res_ordering                          kbo
% 6.81/1.50  --res_to_prop_solver                    active
% 6.81/1.50  --res_prop_simpl_new                    false
% 6.81/1.50  --res_prop_simpl_given                  true
% 6.81/1.50  --res_passive_queue_type                priority_queues
% 6.81/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.50  --res_passive_queues_freq               [15;5]
% 6.81/1.50  --res_forward_subs                      full
% 6.81/1.50  --res_backward_subs                     full
% 6.81/1.50  --res_forward_subs_resolution           true
% 6.81/1.50  --res_backward_subs_resolution          true
% 6.81/1.50  --res_orphan_elimination                true
% 6.81/1.50  --res_time_limit                        2.
% 6.81/1.50  --res_out_proof                         true
% 6.81/1.50  
% 6.81/1.50  ------ Superposition Options
% 6.81/1.50  
% 6.81/1.50  --superposition_flag                    true
% 6.81/1.50  --sup_passive_queue_type                priority_queues
% 6.81/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.50  --demod_completeness_check              fast
% 6.81/1.50  --demod_use_ground                      true
% 6.81/1.50  --sup_to_prop_solver                    passive
% 6.81/1.50  --sup_prop_simpl_new                    true
% 6.81/1.50  --sup_prop_simpl_given                  true
% 6.81/1.50  --sup_fun_splitting                     false
% 6.81/1.50  --sup_smt_interval                      50000
% 6.81/1.50  
% 6.81/1.50  ------ Superposition Simplification Setup
% 6.81/1.50  
% 6.81/1.50  --sup_indices_passive                   []
% 6.81/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_full_bw                           [BwDemod]
% 6.81/1.50  --sup_immed_triv                        [TrivRules]
% 6.81/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_immed_bw_main                     []
% 6.81/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.50  
% 6.81/1.50  ------ Combination Options
% 6.81/1.50  
% 6.81/1.50  --comb_res_mult                         3
% 6.81/1.50  --comb_sup_mult                         2
% 6.81/1.50  --comb_inst_mult                        10
% 6.81/1.50  
% 6.81/1.50  ------ Debug Options
% 6.81/1.50  
% 6.81/1.50  --dbg_backtrace                         false
% 6.81/1.50  --dbg_dump_prop_clauses                 false
% 6.81/1.50  --dbg_dump_prop_clauses_file            -
% 6.81/1.50  --dbg_out_stat                          false
% 6.81/1.50  ------ Parsing...
% 6.81/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.81/1.50  
% 6.81/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.81/1.50  
% 6.81/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.81/1.50  
% 6.81/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.81/1.50  ------ Proving...
% 6.81/1.50  ------ Problem Properties 
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  clauses                                 26
% 6.81/1.50  conjectures                             2
% 6.81/1.50  EPR                                     3
% 6.81/1.50  Horn                                    22
% 6.81/1.50  unary                                   11
% 6.81/1.50  binary                                  6
% 6.81/1.50  lits                                    54
% 6.81/1.50  lits eq                                 21
% 6.81/1.50  fd_pure                                 0
% 6.81/1.50  fd_pseudo                               0
% 6.81/1.50  fd_cond                                 1
% 6.81/1.50  fd_pseudo_cond                          5
% 6.81/1.50  AC symbols                              0
% 6.81/1.50  
% 6.81/1.50  ------ Schedule dynamic 5 is on 
% 6.81/1.50  
% 6.81/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  ------ 
% 6.81/1.50  Current options:
% 6.81/1.50  ------ 
% 6.81/1.50  
% 6.81/1.50  ------ Input Options
% 6.81/1.50  
% 6.81/1.50  --out_options                           all
% 6.81/1.50  --tptp_safe_out                         true
% 6.81/1.50  --problem_path                          ""
% 6.81/1.50  --include_path                          ""
% 6.81/1.50  --clausifier                            res/vclausify_rel
% 6.81/1.50  --clausifier_options                    --mode clausify
% 6.81/1.50  --stdin                                 false
% 6.81/1.50  --stats_out                             all
% 6.81/1.50  
% 6.81/1.50  ------ General Options
% 6.81/1.50  
% 6.81/1.50  --fof                                   false
% 6.81/1.50  --time_out_real                         305.
% 6.81/1.50  --time_out_virtual                      -1.
% 6.81/1.50  --symbol_type_check                     false
% 6.81/1.50  --clausify_out                          false
% 6.81/1.50  --sig_cnt_out                           false
% 6.81/1.50  --trig_cnt_out                          false
% 6.81/1.50  --trig_cnt_out_tolerance                1.
% 6.81/1.50  --trig_cnt_out_sk_spl                   false
% 6.81/1.50  --abstr_cl_out                          false
% 6.81/1.50  
% 6.81/1.50  ------ Global Options
% 6.81/1.50  
% 6.81/1.50  --schedule                              default
% 6.81/1.50  --add_important_lit                     false
% 6.81/1.50  --prop_solver_per_cl                    1000
% 6.81/1.50  --min_unsat_core                        false
% 6.81/1.50  --soft_assumptions                      false
% 6.81/1.50  --soft_lemma_size                       3
% 6.81/1.50  --prop_impl_unit_size                   0
% 6.81/1.50  --prop_impl_unit                        []
% 6.81/1.50  --share_sel_clauses                     true
% 6.81/1.50  --reset_solvers                         false
% 6.81/1.50  --bc_imp_inh                            [conj_cone]
% 6.81/1.50  --conj_cone_tolerance                   3.
% 6.81/1.50  --extra_neg_conj                        none
% 6.81/1.50  --large_theory_mode                     true
% 6.81/1.50  --prolific_symb_bound                   200
% 6.81/1.50  --lt_threshold                          2000
% 6.81/1.50  --clause_weak_htbl                      true
% 6.81/1.50  --gc_record_bc_elim                     false
% 6.81/1.50  
% 6.81/1.50  ------ Preprocessing Options
% 6.81/1.50  
% 6.81/1.50  --preprocessing_flag                    true
% 6.81/1.50  --time_out_prep_mult                    0.1
% 6.81/1.50  --splitting_mode                        input
% 6.81/1.50  --splitting_grd                         true
% 6.81/1.50  --splitting_cvd                         false
% 6.81/1.50  --splitting_cvd_svl                     false
% 6.81/1.50  --splitting_nvd                         32
% 6.81/1.50  --sub_typing                            true
% 6.81/1.50  --prep_gs_sim                           true
% 6.81/1.50  --prep_unflatten                        true
% 6.81/1.50  --prep_res_sim                          true
% 6.81/1.50  --prep_upred                            true
% 6.81/1.50  --prep_sem_filter                       exhaustive
% 6.81/1.50  --prep_sem_filter_out                   false
% 6.81/1.50  --pred_elim                             true
% 6.81/1.50  --res_sim_input                         true
% 6.81/1.50  --eq_ax_congr_red                       true
% 6.81/1.50  --pure_diseq_elim                       true
% 6.81/1.50  --brand_transform                       false
% 6.81/1.50  --non_eq_to_eq                          false
% 6.81/1.50  --prep_def_merge                        true
% 6.81/1.50  --prep_def_merge_prop_impl              false
% 6.81/1.50  --prep_def_merge_mbd                    true
% 6.81/1.50  --prep_def_merge_tr_red                 false
% 6.81/1.50  --prep_def_merge_tr_cl                  false
% 6.81/1.50  --smt_preprocessing                     true
% 6.81/1.50  --smt_ac_axioms                         fast
% 6.81/1.50  --preprocessed_out                      false
% 6.81/1.50  --preprocessed_stats                    false
% 6.81/1.50  
% 6.81/1.50  ------ Abstraction refinement Options
% 6.81/1.50  
% 6.81/1.50  --abstr_ref                             []
% 6.81/1.50  --abstr_ref_prep                        false
% 6.81/1.50  --abstr_ref_until_sat                   false
% 6.81/1.50  --abstr_ref_sig_restrict                funpre
% 6.81/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.50  --abstr_ref_under                       []
% 6.81/1.50  
% 6.81/1.50  ------ SAT Options
% 6.81/1.50  
% 6.81/1.50  --sat_mode                              false
% 6.81/1.50  --sat_fm_restart_options                ""
% 6.81/1.50  --sat_gr_def                            false
% 6.81/1.50  --sat_epr_types                         true
% 6.81/1.50  --sat_non_cyclic_types                  false
% 6.81/1.50  --sat_finite_models                     false
% 6.81/1.50  --sat_fm_lemmas                         false
% 6.81/1.50  --sat_fm_prep                           false
% 6.81/1.50  --sat_fm_uc_incr                        true
% 6.81/1.50  --sat_out_model                         small
% 6.81/1.50  --sat_out_clauses                       false
% 6.81/1.50  
% 6.81/1.50  ------ QBF Options
% 6.81/1.50  
% 6.81/1.50  --qbf_mode                              false
% 6.81/1.50  --qbf_elim_univ                         false
% 6.81/1.50  --qbf_dom_inst                          none
% 6.81/1.50  --qbf_dom_pre_inst                      false
% 6.81/1.50  --qbf_sk_in                             false
% 6.81/1.50  --qbf_pred_elim                         true
% 6.81/1.50  --qbf_split                             512
% 6.81/1.50  
% 6.81/1.50  ------ BMC1 Options
% 6.81/1.50  
% 6.81/1.50  --bmc1_incremental                      false
% 6.81/1.50  --bmc1_axioms                           reachable_all
% 6.81/1.50  --bmc1_min_bound                        0
% 6.81/1.50  --bmc1_max_bound                        -1
% 6.81/1.50  --bmc1_max_bound_default                -1
% 6.81/1.50  --bmc1_symbol_reachability              true
% 6.81/1.50  --bmc1_property_lemmas                  false
% 6.81/1.50  --bmc1_k_induction                      false
% 6.81/1.50  --bmc1_non_equiv_states                 false
% 6.81/1.50  --bmc1_deadlock                         false
% 6.81/1.50  --bmc1_ucm                              false
% 6.81/1.50  --bmc1_add_unsat_core                   none
% 6.81/1.50  --bmc1_unsat_core_children              false
% 6.81/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.50  --bmc1_out_stat                         full
% 6.81/1.50  --bmc1_ground_init                      false
% 6.81/1.50  --bmc1_pre_inst_next_state              false
% 6.81/1.50  --bmc1_pre_inst_state                   false
% 6.81/1.50  --bmc1_pre_inst_reach_state             false
% 6.81/1.50  --bmc1_out_unsat_core                   false
% 6.81/1.50  --bmc1_aig_witness_out                  false
% 6.81/1.50  --bmc1_verbose                          false
% 6.81/1.50  --bmc1_dump_clauses_tptp                false
% 6.81/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.50  --bmc1_dump_file                        -
% 6.81/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.50  --bmc1_ucm_extend_mode                  1
% 6.81/1.50  --bmc1_ucm_init_mode                    2
% 6.81/1.50  --bmc1_ucm_cone_mode                    none
% 6.81/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.50  --bmc1_ucm_relax_model                  4
% 6.81/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.50  --bmc1_ucm_layered_model                none
% 6.81/1.50  --bmc1_ucm_max_lemma_size               10
% 6.81/1.50  
% 6.81/1.50  ------ AIG Options
% 6.81/1.50  
% 6.81/1.50  --aig_mode                              false
% 6.81/1.50  
% 6.81/1.50  ------ Instantiation Options
% 6.81/1.50  
% 6.81/1.50  --instantiation_flag                    true
% 6.81/1.50  --inst_sos_flag                         false
% 6.81/1.50  --inst_sos_phase                        true
% 6.81/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.50  --inst_lit_sel_side                     none
% 6.81/1.50  --inst_solver_per_active                1400
% 6.81/1.50  --inst_solver_calls_frac                1.
% 6.81/1.50  --inst_passive_queue_type               priority_queues
% 6.81/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.50  --inst_passive_queues_freq              [25;2]
% 6.81/1.50  --inst_dismatching                      true
% 6.81/1.50  --inst_eager_unprocessed_to_passive     true
% 6.81/1.50  --inst_prop_sim_given                   true
% 6.81/1.50  --inst_prop_sim_new                     false
% 6.81/1.50  --inst_subs_new                         false
% 6.81/1.50  --inst_eq_res_simp                      false
% 6.81/1.50  --inst_subs_given                       false
% 6.81/1.50  --inst_orphan_elimination               true
% 6.81/1.50  --inst_learning_loop_flag               true
% 6.81/1.50  --inst_learning_start                   3000
% 6.81/1.50  --inst_learning_factor                  2
% 6.81/1.50  --inst_start_prop_sim_after_learn       3
% 6.81/1.50  --inst_sel_renew                        solver
% 6.81/1.50  --inst_lit_activity_flag                true
% 6.81/1.50  --inst_restr_to_given                   false
% 6.81/1.50  --inst_activity_threshold               500
% 6.81/1.50  --inst_out_proof                        true
% 6.81/1.50  
% 6.81/1.50  ------ Resolution Options
% 6.81/1.50  
% 6.81/1.50  --resolution_flag                       false
% 6.81/1.50  --res_lit_sel                           adaptive
% 6.81/1.50  --res_lit_sel_side                      none
% 6.81/1.50  --res_ordering                          kbo
% 6.81/1.50  --res_to_prop_solver                    active
% 6.81/1.50  --res_prop_simpl_new                    false
% 6.81/1.50  --res_prop_simpl_given                  true
% 6.81/1.50  --res_passive_queue_type                priority_queues
% 6.81/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.50  --res_passive_queues_freq               [15;5]
% 6.81/1.50  --res_forward_subs                      full
% 6.81/1.50  --res_backward_subs                     full
% 6.81/1.50  --res_forward_subs_resolution           true
% 6.81/1.50  --res_backward_subs_resolution          true
% 6.81/1.50  --res_orphan_elimination                true
% 6.81/1.50  --res_time_limit                        2.
% 6.81/1.50  --res_out_proof                         true
% 6.81/1.50  
% 6.81/1.50  ------ Superposition Options
% 6.81/1.50  
% 6.81/1.50  --superposition_flag                    true
% 6.81/1.50  --sup_passive_queue_type                priority_queues
% 6.81/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.50  --demod_completeness_check              fast
% 6.81/1.50  --demod_use_ground                      true
% 6.81/1.50  --sup_to_prop_solver                    passive
% 6.81/1.50  --sup_prop_simpl_new                    true
% 6.81/1.50  --sup_prop_simpl_given                  true
% 6.81/1.50  --sup_fun_splitting                     false
% 6.81/1.50  --sup_smt_interval                      50000
% 6.81/1.50  
% 6.81/1.50  ------ Superposition Simplification Setup
% 6.81/1.50  
% 6.81/1.50  --sup_indices_passive                   []
% 6.81/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_full_bw                           [BwDemod]
% 6.81/1.50  --sup_immed_triv                        [TrivRules]
% 6.81/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_immed_bw_main                     []
% 6.81/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.50  
% 6.81/1.50  ------ Combination Options
% 6.81/1.50  
% 6.81/1.50  --comb_res_mult                         3
% 6.81/1.50  --comb_sup_mult                         2
% 6.81/1.50  --comb_inst_mult                        10
% 6.81/1.50  
% 6.81/1.50  ------ Debug Options
% 6.81/1.50  
% 6.81/1.50  --dbg_backtrace                         false
% 6.81/1.50  --dbg_dump_prop_clauses                 false
% 6.81/1.50  --dbg_dump_prop_clauses_file            -
% 6.81/1.50  --dbg_out_stat                          false
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  ------ Proving...
% 6.81/1.50  
% 6.81/1.50  
% 6.81/1.50  % SZS status Theorem for theBenchmark.p
% 6.81/1.50  
% 6.81/1.50   Resolution empty clause
% 6.81/1.50  
% 6.81/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.81/1.50  
% 6.81/1.50  fof(f10,axiom,(
% 6.81/1.50    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f18,plain,(
% 6.81/1.50    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.81/1.50    inference(ennf_transformation,[],[f10])).
% 6.81/1.50  
% 6.81/1.50  fof(f39,plain,(
% 6.81/1.50    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK6(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f40,plain,(
% 6.81/1.50    ! [X0] : (! [X2] : (k1_funct_1(sK6(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 6.81/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f39])).
% 6.81/1.50  
% 6.81/1.50  fof(f65,plain,(
% 6.81/1.50    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 6.81/1.50    inference(cnf_transformation,[],[f40])).
% 6.81/1.50  
% 6.81/1.50  fof(f9,axiom,(
% 6.81/1.50    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f17,plain,(
% 6.81/1.50    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 6.81/1.50    inference(ennf_transformation,[],[f9])).
% 6.81/1.50  
% 6.81/1.50  fof(f37,plain,(
% 6.81/1.50    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f38,plain,(
% 6.81/1.50    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 6.81/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f37])).
% 6.81/1.50  
% 6.81/1.50  fof(f61,plain,(
% 6.81/1.50    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 6.81/1.50    inference(cnf_transformation,[],[f38])).
% 6.81/1.50  
% 6.81/1.50  fof(f11,conjecture,(
% 6.81/1.50    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f12,negated_conjecture,(
% 6.81/1.50    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 6.81/1.50    inference(negated_conjecture,[],[f11])).
% 6.81/1.50  
% 6.81/1.50  fof(f19,plain,(
% 6.81/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 6.81/1.50    inference(ennf_transformation,[],[f12])).
% 6.81/1.50  
% 6.81/1.50  fof(f20,plain,(
% 6.81/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.81/1.50    inference(flattening,[],[f19])).
% 6.81/1.50  
% 6.81/1.50  fof(f41,plain,(
% 6.81/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK7 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f42,plain,(
% 6.81/1.50    k1_xboole_0 != sK7 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.81/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f41])).
% 6.81/1.50  
% 6.81/1.50  fof(f67,plain,(
% 6.81/1.50    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.81/1.50    inference(cnf_transformation,[],[f42])).
% 6.81/1.50  
% 6.81/1.50  fof(f59,plain,(
% 6.81/1.50    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 6.81/1.50    inference(cnf_transformation,[],[f38])).
% 6.81/1.50  
% 6.81/1.50  fof(f60,plain,(
% 6.81/1.50    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 6.81/1.50    inference(cnf_transformation,[],[f38])).
% 6.81/1.50  
% 6.81/1.50  fof(f63,plain,(
% 6.81/1.50    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 6.81/1.50    inference(cnf_transformation,[],[f40])).
% 6.81/1.50  
% 6.81/1.50  fof(f64,plain,(
% 6.81/1.50    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 6.81/1.50    inference(cnf_transformation,[],[f40])).
% 6.81/1.50  
% 6.81/1.50  fof(f6,axiom,(
% 6.81/1.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f30,plain,(
% 6.81/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 6.81/1.50    inference(nnf_transformation,[],[f6])).
% 6.81/1.50  
% 6.81/1.50  fof(f31,plain,(
% 6.81/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.81/1.50    inference(rectify,[],[f30])).
% 6.81/1.50  
% 6.81/1.50  fof(f34,plain,(
% 6.81/1.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f33,plain,(
% 6.81/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f32,plain,(
% 6.81/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 6.81/1.50    introduced(choice_axiom,[])).
% 6.81/1.50  
% 6.81/1.50  fof(f35,plain,(
% 6.81/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.81/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 6.81/1.50  
% 6.81/1.50  fof(f54,plain,(
% 6.81/1.50    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 6.81/1.50    inference(cnf_transformation,[],[f35])).
% 6.81/1.50  
% 6.81/1.50  fof(f53,plain,(
% 6.81/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 6.81/1.50    inference(cnf_transformation,[],[f35])).
% 6.81/1.50  
% 6.81/1.50  fof(f71,plain,(
% 6.81/1.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 6.81/1.50    inference(equality_resolution,[],[f53])).
% 6.81/1.50  
% 6.81/1.50  fof(f4,axiom,(
% 6.81/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f28,plain,(
% 6.81/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.81/1.50    inference(nnf_transformation,[],[f4])).
% 6.81/1.50  
% 6.81/1.50  fof(f29,plain,(
% 6.81/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.81/1.50    inference(flattening,[],[f28])).
% 6.81/1.50  
% 6.81/1.50  fof(f50,plain,(
% 6.81/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.81/1.50    inference(cnf_transformation,[],[f29])).
% 6.81/1.50  
% 6.81/1.50  fof(f69,plain,(
% 6.81/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.81/1.50    inference(equality_resolution,[],[f50])).
% 6.81/1.50  
% 6.81/1.50  fof(f5,axiom,(
% 6.81/1.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f51,plain,(
% 6.81/1.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 6.81/1.50    inference(cnf_transformation,[],[f5])).
% 6.81/1.50  
% 6.81/1.50  fof(f68,plain,(
% 6.81/1.50    k1_xboole_0 != sK7),
% 6.81/1.50    inference(cnf_transformation,[],[f42])).
% 6.81/1.50  
% 6.81/1.50  fof(f48,plain,(
% 6.81/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 6.81/1.50    inference(cnf_transformation,[],[f29])).
% 6.81/1.50  
% 6.81/1.50  fof(f49,plain,(
% 6.81/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.81/1.50    inference(cnf_transformation,[],[f29])).
% 6.81/1.50  
% 6.81/1.50  fof(f70,plain,(
% 6.81/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.81/1.50    inference(equality_resolution,[],[f49])).
% 6.81/1.50  
% 6.81/1.50  fof(f2,axiom,(
% 6.81/1.50    v1_xboole_0(k1_xboole_0)),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f45,plain,(
% 6.81/1.50    v1_xboole_0(k1_xboole_0)),
% 6.81/1.50    inference(cnf_transformation,[],[f2])).
% 6.81/1.50  
% 6.81/1.50  fof(f8,axiom,(
% 6.81/1.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 6.81/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.50  
% 6.81/1.50  fof(f16,plain,(
% 6.81/1.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.81/1.51    inference(ennf_transformation,[],[f8])).
% 6.81/1.51  
% 6.81/1.51  fof(f36,plain,(
% 6.81/1.51    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.81/1.51    inference(nnf_transformation,[],[f16])).
% 6.81/1.51  
% 6.81/1.51  fof(f57,plain,(
% 6.81/1.51    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.81/1.51    inference(cnf_transformation,[],[f36])).
% 6.81/1.51  
% 6.81/1.51  fof(f7,axiom,(
% 6.81/1.51    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 6.81/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.51  
% 6.81/1.51  fof(f14,plain,(
% 6.81/1.51    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 6.81/1.51    inference(ennf_transformation,[],[f7])).
% 6.81/1.51  
% 6.81/1.51  fof(f15,plain,(
% 6.81/1.51    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 6.81/1.51    inference(flattening,[],[f14])).
% 6.81/1.51  
% 6.81/1.51  fof(f56,plain,(
% 6.81/1.51    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 6.81/1.51    inference(cnf_transformation,[],[f15])).
% 6.81/1.51  
% 6.81/1.51  fof(f52,plain,(
% 6.81/1.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 6.81/1.51    inference(cnf_transformation,[],[f35])).
% 6.81/1.51  
% 6.81/1.51  fof(f72,plain,(
% 6.81/1.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 6.81/1.51    inference(equality_resolution,[],[f52])).
% 6.81/1.51  
% 6.81/1.51  fof(f1,axiom,(
% 6.81/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.81/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.51  
% 6.81/1.51  fof(f21,plain,(
% 6.81/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.81/1.51    inference(nnf_transformation,[],[f1])).
% 6.81/1.51  
% 6.81/1.51  fof(f22,plain,(
% 6.81/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.81/1.51    inference(rectify,[],[f21])).
% 6.81/1.51  
% 6.81/1.51  fof(f23,plain,(
% 6.81/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.81/1.51    introduced(choice_axiom,[])).
% 6.81/1.51  
% 6.81/1.51  fof(f24,plain,(
% 6.81/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.81/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 6.81/1.51  
% 6.81/1.51  fof(f43,plain,(
% 6.81/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.81/1.51    inference(cnf_transformation,[],[f24])).
% 6.81/1.51  
% 6.81/1.51  fof(f62,plain,(
% 6.81/1.51    ( ! [X0,X3,X1] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 6.81/1.51    inference(cnf_transformation,[],[f38])).
% 6.81/1.51  
% 6.81/1.51  cnf(c_21,plain,
% 6.81/1.51      ( k1_relat_1(sK6(X0)) = X0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f65]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_17,plain,
% 6.81/1.51      ( k1_relat_1(sK5(X0,X1)) = X0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_25,negated_conjecture,
% 6.81/1.51      ( ~ v1_funct_1(X0)
% 6.81/1.51      | ~ v1_funct_1(X1)
% 6.81/1.51      | ~ v1_relat_1(X0)
% 6.81/1.51      | ~ v1_relat_1(X1)
% 6.81/1.51      | X1 = X0
% 6.81/1.51      | k1_relat_1(X0) != sK7
% 6.81/1.51      | k1_relat_1(X1) != sK7 ),
% 6.81/1.51      inference(cnf_transformation,[],[f67]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_608,plain,
% 6.81/1.51      ( X0 = X1
% 6.81/1.51      | k1_relat_1(X0) != sK7
% 6.81/1.51      | k1_relat_1(X1) != sK7
% 6.81/1.51      | v1_funct_1(X1) != iProver_top
% 6.81/1.51      | v1_funct_1(X0) != iProver_top
% 6.81/1.51      | v1_relat_1(X1) != iProver_top
% 6.81/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1053,plain,
% 6.81/1.51      ( sK5(X0,X1) = X2
% 6.81/1.51      | k1_relat_1(X2) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X2) != iProver_top
% 6.81/1.51      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 6.81/1.51      | v1_relat_1(X2) != iProver_top
% 6.81/1.51      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_17,c_608]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_19,plain,
% 6.81/1.51      ( v1_relat_1(sK5(X0,X1)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_39,plain,
% 6.81/1.51      ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_18,plain,
% 6.81/1.51      ( v1_funct_1(sK5(X0,X1)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_42,plain,
% 6.81/1.51      ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1169,plain,
% 6.81/1.51      ( v1_relat_1(X2) != iProver_top
% 6.81/1.51      | sK5(X0,X1) = X2
% 6.81/1.51      | k1_relat_1(X2) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X2) != iProver_top ),
% 6.81/1.51      inference(global_propositional_subsumption,
% 6.81/1.51                [status(thm)],
% 6.81/1.51                [c_1053,c_39,c_42]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1170,plain,
% 6.81/1.51      ( sK5(X0,X1) = X2
% 6.81/1.51      | k1_relat_1(X2) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X2) != iProver_top
% 6.81/1.51      | v1_relat_1(X2) != iProver_top ),
% 6.81/1.51      inference(renaming,[status(thm)],[c_1169]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1181,plain,
% 6.81/1.51      ( sK5(X0,X1) = sK6(X2)
% 6.81/1.51      | sK7 != X2
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(sK6(X2)) != iProver_top
% 6.81/1.51      | v1_relat_1(sK6(X2)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_21,c_1170]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_836,plain,
% 6.81/1.51      ( sK6(X0) = X1
% 6.81/1.51      | k1_relat_1(X1) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X1) != iProver_top
% 6.81/1.51      | v1_funct_1(sK6(X0)) != iProver_top
% 6.81/1.51      | v1_relat_1(X1) != iProver_top
% 6.81/1.51      | v1_relat_1(sK6(X0)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_21,c_608]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_23,plain,
% 6.81/1.51      ( v1_relat_1(sK6(X0)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f63]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_29,plain,
% 6.81/1.51      ( v1_relat_1(sK6(X0)) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_22,plain,
% 6.81/1.51      ( v1_funct_1(sK6(X0)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_32,plain,
% 6.81/1.51      ( v1_funct_1(sK6(X0)) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_855,plain,
% 6.81/1.51      ( v1_relat_1(X1) != iProver_top
% 6.81/1.51      | sK6(X0) = X1
% 6.81/1.51      | k1_relat_1(X1) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X1) != iProver_top ),
% 6.81/1.51      inference(global_propositional_subsumption,
% 6.81/1.51                [status(thm)],
% 6.81/1.51                [c_836,c_29,c_32]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_856,plain,
% 6.81/1.51      ( sK6(X0) = X1
% 6.81/1.51      | k1_relat_1(X1) != sK7
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | v1_funct_1(X1) != iProver_top
% 6.81/1.51      | v1_relat_1(X1) != iProver_top ),
% 6.81/1.51      inference(renaming,[status(thm)],[c_855]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1052,plain,
% 6.81/1.51      ( sK5(X0,X1) = sK6(X2)
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | sK7 != X2
% 6.81/1.51      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 6.81/1.51      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_17,c_856]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1078,plain,
% 6.81/1.51      ( ~ v1_funct_1(sK5(X0,X1))
% 6.81/1.51      | ~ v1_relat_1(sK5(X0,X1))
% 6.81/1.51      | sK5(X0,X1) = sK6(X2)
% 6.81/1.51      | sK7 != X0
% 6.81/1.51      | sK7 != X2 ),
% 6.81/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_1052]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1232,plain,
% 6.81/1.51      ( sK5(X0,X1) = sK6(X2) | sK7 != X2 | sK7 != X0 ),
% 6.81/1.51      inference(global_propositional_subsumption,
% 6.81/1.51                [status(thm)],
% 6.81/1.51                [c_1181,c_19,c_18,c_1078]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1233,plain,
% 6.81/1.51      ( sK5(X0,X1) = sK6(X2) | sK7 != X0 | sK7 != X2 ),
% 6.81/1.51      inference(renaming,[status(thm)],[c_1232]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1238,plain,
% 6.81/1.51      ( sK5(sK7,X0) = sK6(X1) | sK7 != X1 ),
% 6.81/1.51      inference(equality_resolution,[status(thm)],[c_1233]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1273,plain,
% 6.81/1.51      ( sK5(sK7,X0) = sK6(sK7) ),
% 6.81/1.51      inference(equality_resolution,[status(thm)],[c_1238]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_10,plain,
% 6.81/1.51      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 6.81/1.51      | r2_hidden(sK2(X0,X1),X1)
% 6.81/1.51      | k1_relat_1(X0) = X1 ),
% 6.81/1.51      inference(cnf_transformation,[],[f54]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_620,plain,
% 6.81/1.51      ( k1_relat_1(X0) = X1
% 6.81/1.51      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_11,plain,
% 6.81/1.51      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 6.81/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_619,plain,
% 6.81/1.51      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 6.81/1.51      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2898,plain,
% 6.81/1.51      ( k1_relat_1(X0) = X1
% 6.81/1.51      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_620,c_619]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_10436,plain,
% 6.81/1.51      ( k1_relat_1(sK5(X0,X1)) = X2
% 6.81/1.51      | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(sK5(X0,X1),X2),X2) = iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_17,c_2898]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_10656,plain,
% 6.81/1.51      ( X0 = X1
% 6.81/1.51      | r2_hidden(sK2(sK5(X1,X2),X0),X1) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(sK5(X1,X2),X0),X0) = iProver_top ),
% 6.81/1.51      inference(demodulation,[status(thm)],[c_10436,c_17]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_14555,plain,
% 6.81/1.51      ( sK7 = X0
% 6.81/1.51      | r2_hidden(sK2(sK5(sK7,X1),X0),X0) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_1273,c_10656]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_14921,plain,
% 6.81/1.51      ( sK7 = X0
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),X0),X0) = iProver_top
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top ),
% 6.81/1.51      inference(demodulation,[status(thm)],[c_14555,c_1273]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_5,plain,
% 6.81/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_8,plain,
% 6.81/1.51      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f51]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_622,plain,
% 6.81/1.51      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1475,plain,
% 6.81/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_5,c_622]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_15101,plain,
% 6.81/1.51      ( sK7 = k1_xboole_0
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_14921,c_1475]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_24,negated_conjecture,
% 6.81/1.51      ( k1_xboole_0 != sK7 ),
% 6.81/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_31,plain,
% 6.81/1.51      ( v1_relat_1(sK6(k1_xboole_0)) = iProver_top ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_7,plain,
% 6.81/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 6.81/1.51      | k1_xboole_0 = X1
% 6.81/1.51      | k1_xboole_0 = X0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_73,plain,
% 6.81/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.81/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_6,plain,
% 6.81/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_74,plain,
% 6.81/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2,plain,
% 6.81/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 6.81/1.51      inference(cnf_transformation,[],[f45]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_81,plain,
% 6.81/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_245,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_826,plain,
% 6.81/1.51      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_245]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_827,plain,
% 6.81/1.51      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_826]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_15,plain,
% 6.81/1.51      ( ~ v1_relat_1(X0)
% 6.81/1.51      | k2_relat_1(X0) = k1_xboole_0
% 6.81/1.51      | k1_relat_1(X0) != k1_xboole_0 ),
% 6.81/1.51      inference(cnf_transformation,[],[f57]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_615,plain,
% 6.81/1.51      ( k2_relat_1(X0) = k1_xboole_0
% 6.81/1.51      | k1_relat_1(X0) != k1_xboole_0
% 6.81/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1917,plain,
% 6.81/1.51      ( k2_relat_1(sK6(X0)) = k1_xboole_0
% 6.81/1.51      | k1_xboole_0 != X0
% 6.81/1.51      | v1_relat_1(sK6(X0)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_21,c_615]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2244,plain,
% 6.81/1.51      ( k1_xboole_0 != X0 | k2_relat_1(sK6(X0)) = k1_xboole_0 ),
% 6.81/1.51      inference(global_propositional_subsumption,[status(thm)],[c_1917,c_29]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2245,plain,
% 6.81/1.51      ( k2_relat_1(sK6(X0)) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 6.81/1.51      inference(renaming,[status(thm)],[c_2244]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2249,plain,
% 6.81/1.51      ( k2_relat_1(sK6(k1_xboole_0)) = k1_xboole_0 ),
% 6.81/1.51      inference(equality_resolution,[status(thm)],[c_2245]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_13,plain,
% 6.81/1.51      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 6.81/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_617,plain,
% 6.81/1.51      ( v1_relat_1(X0) != iProver_top
% 6.81/1.51      | v1_xboole_0(X0) = iProver_top
% 6.81/1.51      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2355,plain,
% 6.81/1.51      ( v1_relat_1(sK6(k1_xboole_0)) != iProver_top
% 6.81/1.51      | v1_xboole_0(sK6(k1_xboole_0)) = iProver_top
% 6.81/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_2249,c_617]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_12,plain,
% 6.81/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.81/1.51      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 6.81/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_618,plain,
% 6.81/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.81/1.51      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_1,plain,
% 6.81/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.81/1.51      inference(cnf_transformation,[],[f43]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_626,plain,
% 6.81/1.51      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_2213,plain,
% 6.81/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.81/1.51      | v1_xboole_0(X1) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_618,c_626]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_3665,plain,
% 6.81/1.51      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(sK6(X1)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_21,c_2213]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_15091,plain,
% 6.81/1.51      ( sK7 = X0
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),X0),sK7) = iProver_top
% 6.81/1.51      | v1_xboole_0(sK6(X0)) != iProver_top ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_14921,c_3665]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_15326,plain,
% 6.81/1.51      ( sK7 = k1_xboole_0
% 6.81/1.51      | r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top
% 6.81/1.51      | v1_xboole_0(sK6(k1_xboole_0)) != iProver_top ),
% 6.81/1.51      inference(instantiation,[status(thm)],[c_15091]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_16026,plain,
% 6.81/1.51      ( r2_hidden(sK2(sK6(sK7),k1_xboole_0),sK7) = iProver_top ),
% 6.81/1.51      inference(global_propositional_subsumption,
% 6.81/1.51                [status(thm)],
% 6.81/1.51                [c_15101,c_24,c_31,c_73,c_74,c_81,c_827,c_2355,c_15326]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_16,plain,
% 6.81/1.51      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1,X2),X0) = X2 ),
% 6.81/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_614,plain,
% 6.81/1.51      ( k1_funct_1(sK5(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 6.81/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_16038,plain,
% 6.81/1.51      ( k1_funct_1(sK5(sK7,X0),sK2(sK6(sK7),k1_xboole_0)) = X0 ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_16026,c_614]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_16040,plain,
% 6.81/1.51      ( k1_funct_1(sK6(sK7),sK2(sK6(sK7),k1_xboole_0)) = X0 ),
% 6.81/1.51      inference(light_normalisation,[status(thm)],[c_16038,c_1273]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_16166,plain,
% 6.81/1.51      ( X0 = X1 ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_16040,c_16040]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_17488,plain,
% 6.81/1.51      ( k1_xboole_0 != X0 ),
% 6.81/1.51      inference(superposition,[status(thm)],[c_16166,c_24]) ).
% 6.81/1.51  
% 6.81/1.51  cnf(c_17504,plain,
% 6.81/1.51      ( $false ),
% 6.81/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_17488,c_16166]) ).
% 6.81/1.51  
% 6.81/1.51  
% 6.81/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.81/1.51  
% 6.81/1.51  ------                               Statistics
% 6.81/1.51  
% 6.81/1.51  ------ General
% 6.81/1.51  
% 6.81/1.51  abstr_ref_over_cycles:                  0
% 6.81/1.51  abstr_ref_under_cycles:                 0
% 6.81/1.51  gc_basic_clause_elim:                   0
% 6.81/1.51  forced_gc_time:                         0
% 6.81/1.51  parsing_time:                           0.009
% 6.81/1.51  unif_index_cands_time:                  0.
% 6.81/1.51  unif_index_add_time:                    0.
% 6.81/1.51  orderings_time:                         0.
% 6.81/1.51  out_proof_time:                         0.024
% 6.81/1.51  total_time:                             0.655
% 6.81/1.51  num_of_symbols:                         50
% 6.81/1.51  num_of_terms:                           13929
% 6.81/1.51  
% 6.81/1.51  ------ Preprocessing
% 6.81/1.51  
% 6.81/1.51  num_of_splits:                          0
% 6.81/1.51  num_of_split_atoms:                     0
% 6.81/1.51  num_of_reused_defs:                     0
% 6.81/1.51  num_eq_ax_congr_red:                    28
% 6.81/1.51  num_of_sem_filtered_clauses:            1
% 6.81/1.51  num_of_subtypes:                        0
% 6.81/1.51  monotx_restored_types:                  0
% 6.81/1.51  sat_num_of_epr_types:                   0
% 6.81/1.51  sat_num_of_non_cyclic_types:            0
% 6.81/1.51  sat_guarded_non_collapsed_types:        0
% 6.81/1.51  num_pure_diseq_elim:                    0
% 6.81/1.51  simp_replaced_by:                       0
% 6.81/1.51  res_preprocessed:                       99
% 6.81/1.51  prep_upred:                             0
% 6.81/1.51  prep_unflattend:                        0
% 6.81/1.51  smt_new_axioms:                         0
% 6.81/1.51  pred_elim_cands:                        4
% 6.81/1.51  pred_elim:                              0
% 6.81/1.51  pred_elim_cl:                           0
% 6.81/1.51  pred_elim_cycles:                       1
% 6.81/1.51  merged_defs:                            0
% 6.81/1.51  merged_defs_ncl:                        0
% 6.81/1.51  bin_hyper_res:                          0
% 6.81/1.51  prep_cycles:                            3
% 6.81/1.51  pred_elim_time:                         0.
% 6.81/1.51  splitting_time:                         0.
% 6.81/1.51  sem_filter_time:                        0.
% 6.81/1.51  monotx_time:                            0.
% 6.81/1.51  subtype_inf_time:                       0.
% 6.81/1.51  
% 6.81/1.51  ------ Problem properties
% 6.81/1.51  
% 6.81/1.51  clauses:                                26
% 6.81/1.51  conjectures:                            2
% 6.81/1.51  epr:                                    3
% 6.81/1.51  horn:                                   22
% 6.81/1.51  ground:                                 2
% 6.81/1.51  unary:                                  11
% 6.81/1.51  binary:                                 6
% 6.81/1.51  lits:                                   54
% 6.81/1.51  lits_eq:                                21
% 6.81/1.51  fd_pure:                                0
% 6.81/1.51  fd_pseudo:                              0
% 6.81/1.51  fd_cond:                                1
% 6.81/1.51  fd_pseudo_cond:                         5
% 6.81/1.51  ac_symbols:                             0
% 6.81/1.51  
% 6.81/1.51  ------ Propositional Solver
% 6.81/1.51  
% 6.81/1.51  prop_solver_calls:                      25
% 6.81/1.51  prop_fast_solver_calls:                 819
% 6.81/1.51  smt_solver_calls:                       0
% 6.81/1.51  smt_fast_solver_calls:                  0
% 6.81/1.51  prop_num_of_clauses:                    6246
% 6.81/1.51  prop_preprocess_simplified:             12733
% 6.81/1.51  prop_fo_subsumed:                       29
% 6.81/1.51  prop_solver_time:                       0.
% 6.81/1.51  smt_solver_time:                        0.
% 6.81/1.51  smt_fast_solver_time:                   0.
% 6.81/1.51  prop_fast_solver_time:                  0.
% 6.81/1.51  prop_unsat_core_time:                   0.
% 6.81/1.51  
% 6.81/1.51  ------ QBF
% 6.81/1.51  
% 6.81/1.51  qbf_q_res:                              0
% 6.81/1.51  qbf_num_tautologies:                    0
% 6.81/1.51  qbf_prep_cycles:                        0
% 6.81/1.51  
% 6.81/1.51  ------ BMC1
% 6.81/1.51  
% 6.81/1.51  bmc1_current_bound:                     -1
% 6.81/1.51  bmc1_last_solved_bound:                 -1
% 6.81/1.51  bmc1_unsat_core_size:                   -1
% 6.81/1.51  bmc1_unsat_core_parents_size:           -1
% 6.81/1.51  bmc1_merge_next_fun:                    0
% 6.81/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.81/1.51  
% 6.81/1.51  ------ Instantiation
% 6.81/1.51  
% 6.81/1.51  inst_num_of_clauses:                    1863
% 6.81/1.51  inst_num_in_passive:                    715
% 6.81/1.51  inst_num_in_active:                     629
% 6.81/1.51  inst_num_in_unprocessed:                519
% 6.81/1.51  inst_num_of_loops:                      820
% 6.81/1.51  inst_num_of_learning_restarts:          0
% 6.81/1.51  inst_num_moves_active_passive:          189
% 6.81/1.51  inst_lit_activity:                      0
% 6.81/1.51  inst_lit_activity_moves:                0
% 6.81/1.51  inst_num_tautologies:                   0
% 6.81/1.51  inst_num_prop_implied:                  0
% 6.81/1.51  inst_num_existing_simplified:           0
% 6.81/1.51  inst_num_eq_res_simplified:             0
% 6.81/1.51  inst_num_child_elim:                    0
% 6.81/1.51  inst_num_of_dismatching_blockings:      550
% 6.81/1.51  inst_num_of_non_proper_insts:           1568
% 6.81/1.51  inst_num_of_duplicates:                 0
% 6.81/1.51  inst_inst_num_from_inst_to_res:         0
% 6.81/1.51  inst_dismatching_checking_time:         0.
% 6.81/1.51  
% 6.81/1.51  ------ Resolution
% 6.81/1.51  
% 6.81/1.51  res_num_of_clauses:                     0
% 6.81/1.51  res_num_in_passive:                     0
% 6.81/1.51  res_num_in_active:                      0
% 6.81/1.51  res_num_of_loops:                       102
% 6.81/1.51  res_forward_subset_subsumed:            82
% 6.81/1.51  res_backward_subset_subsumed:           2
% 6.81/1.51  res_forward_subsumed:                   0
% 6.81/1.51  res_backward_subsumed:                  0
% 6.81/1.51  res_forward_subsumption_resolution:     0
% 6.81/1.51  res_backward_subsumption_resolution:    0
% 6.81/1.51  res_clause_to_clause_subsumption:       3425
% 6.81/1.51  res_orphan_elimination:                 0
% 6.81/1.51  res_tautology_del:                      54
% 6.81/1.51  res_num_eq_res_simplified:              0
% 6.81/1.51  res_num_sel_changes:                    0
% 6.81/1.51  res_moves_from_active_to_pass:          0
% 6.81/1.51  
% 6.81/1.51  ------ Superposition
% 6.81/1.51  
% 6.81/1.51  sup_time_total:                         0.
% 6.81/1.51  sup_time_generating:                    0.
% 6.81/1.51  sup_time_sim_full:                      0.
% 6.81/1.51  sup_time_sim_immed:                     0.
% 6.81/1.51  
% 6.81/1.51  sup_num_of_clauses:                     423
% 6.81/1.51  sup_num_in_active:                      15
% 6.81/1.51  sup_num_in_passive:                     408
% 6.81/1.51  sup_num_of_loops:                       162
% 6.81/1.51  sup_fw_superposition:                   370
% 6.81/1.51  sup_bw_superposition:                   640
% 6.81/1.51  sup_immediate_simplified:               260
% 6.81/1.51  sup_given_eliminated:                   2
% 6.81/1.51  comparisons_done:                       0
% 6.81/1.51  comparisons_avoided:                    3
% 6.81/1.51  
% 6.81/1.51  ------ Simplifications
% 6.81/1.51  
% 6.81/1.51  
% 6.81/1.51  sim_fw_subset_subsumed:                 45
% 6.81/1.51  sim_bw_subset_subsumed:                 77
% 6.81/1.51  sim_fw_subsumed:                        241
% 6.81/1.51  sim_bw_subsumed:                        14
% 6.81/1.51  sim_fw_subsumption_res:                 49
% 6.81/1.51  sim_bw_subsumption_res:                 1
% 6.81/1.51  sim_tautology_del:                      14
% 6.81/1.51  sim_eq_tautology_del:                   29
% 6.81/1.51  sim_eq_res_simp:                        3
% 6.81/1.51  sim_fw_demodulated:                     11
% 6.81/1.51  sim_bw_demodulated:                     192
% 6.81/1.51  sim_light_normalised:                   131
% 6.81/1.51  sim_joinable_taut:                      0
% 6.81/1.51  sim_joinable_simp:                      0
% 6.81/1.51  sim_ac_normalised:                      0
% 6.81/1.51  sim_smt_subsumption:                    0
% 6.81/1.51  
%------------------------------------------------------------------------------
