%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:20 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  154 (1155 expanded)
%              Number of clauses        :   94 ( 405 expanded)
%              Number of leaves         :   19 ( 284 expanded)
%              Depth                    :   24
%              Number of atoms          :  524 (5474 expanded)
%              Number of equality atoms :  331 (2850 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK4(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK4(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).

fof(f56,plain,(
    ! [X2,X0] :
      ( k1_funct_1(sK4(X0),X2) = np__1
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f62,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f28])).

fof(f51,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f18])).

fof(f32,plain,
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
   => ( k1_xboole_0 != sK5
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK5
              | k1_relat_1(X1) != sK5
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 != sK5
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK5
            | k1_relat_1(X1) != sK5
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f32])).

fof(f57,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK5
      | k1_relat_1(X1) != sK5
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

cnf(c_7,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_636,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2008,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_636])).

cnf(c_6,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2104,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2008,c_6])).

cnf(c_8,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_66,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_68,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_5,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_69,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_71,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_77,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2880,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2104,c_68,c_71,c_77])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_639,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1463,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_639])).

cnf(c_2887,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2880,c_1463])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1),X0) = np__1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_629,plain,
    ( k1_funct_1(sK4(X0),X1) = np__1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2890,plain,
    ( k1_funct_1(sK4(X0),sK0(k1_xboole_0,X0)) = np__1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2887,c_629])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_635,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4187,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),k1_relat_1(sK4(X0))) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2890,c_635])).

cnf(c_20,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4193,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4187,c_20])).

cnf(c_22,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4217,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4193,c_28,c_31,c_2887])).

cnf(c_16,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != sK5
    | k1_relat_1(X0) != sK5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_626,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK5
    | k1_relat_1(X0) != sK5
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_944,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_626])).

cnf(c_18,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_38,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_41,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1100,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_38,c_41])).

cnf(c_1101,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1100])).

cnf(c_1111,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0
    | v1_funct_1(sK4(X2)) != iProver_top
    | v1_relat_1(sK4(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1101])).

cnf(c_941,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_626])).

cnf(c_1039,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_28,c_31])).

cnf(c_1040,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1039])).

cnf(c_1049,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1040])).

cnf(c_1071,plain,
    ( ~ v1_funct_1(sK3(X0,X1))
    | ~ v1_relat_1(sK3(X0,X1))
    | sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1049])).

cnf(c_1224,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1111,c_18,c_17,c_1071])).

cnf(c_1225,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(renaming,[status(thm)],[c_1224])).

cnf(c_1229,plain,
    ( sK3(sK5,X0) = sK4(X1)
    | sK5 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1225])).

cnf(c_1279,plain,
    ( sK3(sK5,X0) = sK4(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1229])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_633,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1778,plain,
    ( r2_hidden(X0,k2_relat_1(sK3(X1,X2))) != iProver_top
    | r2_hidden(sK2(sK3(X1,X2),X0),X1) = iProver_top
    | v1_funct_1(sK3(X1,X2)) != iProver_top
    | v1_relat_1(sK3(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_633])).

cnf(c_630,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_631,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3154,plain,
    ( r2_hidden(X0,k2_relat_1(sK3(X1,X2))) != iProver_top
    | r2_hidden(sK2(sK3(X1,X2),X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1778,c_630,c_631])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_632,plain,
    ( k1_funct_1(sK3(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3160,plain,
    ( k1_funct_1(sK3(X0,X1),sK2(sK3(X0,X2),X3)) = X1
    | r2_hidden(X3,k2_relat_1(sK3(X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_632])).

cnf(c_4412,plain,
    ( k1_funct_1(sK3(sK5,X0),sK2(sK3(sK5,X1),X2)) = X0
    | r2_hidden(X2,k2_relat_1(sK4(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_3160])).

cnf(c_4415,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK3(sK5,X0),X1)) = X2
    | r2_hidden(X1,k2_relat_1(sK4(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4412,c_1279])).

cnf(c_4416,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),X0)) = X1
    | r2_hidden(X0,k2_relat_1(sK4(sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4415,c_1279])).

cnf(c_4582,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = X0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4217,c_4416])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_75,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_340,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_804,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_805,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_5026,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4582,c_23,c_75,c_76,c_805])).

cnf(c_5081,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = sK4(sK5) ),
    inference(superposition,[status(thm)],[c_5026,c_1279])).

cnf(c_5114,plain,
    ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5026,c_2])).

cnf(c_7917,plain,
    ( sK4(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5081,c_5114])).

cnf(c_3035,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_3036,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_345,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1374,plain,
    ( sK4(sK5) != X0
    | k1_relat_1(sK4(sK5)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1376,plain,
    ( sK4(sK5) != k1_xboole_0
    | k1_relat_1(sK4(sK5)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1161,plain,
    ( k1_relat_1(sK4(sK5)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_1373,plain,
    ( k1_relat_1(sK4(sK5)) != k1_relat_1(X0)
    | k1_xboole_0 != k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1375,plain,
    ( k1_relat_1(sK4(sK5)) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK4(sK5))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_964,plain,
    ( sK5 != k1_relat_1(sK4(sK5))
    | k1_xboole_0 != k1_relat_1(sK4(sK5))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_880,plain,
    ( k1_relat_1(sK4(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_823,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_839,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_879,plain,
    ( k1_relat_1(sK4(sK5)) != sK5
    | sK5 = k1_relat_1(sK4(sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_339,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_840,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7917,c_3036,c_1376,c_1375,c_964,c_880,c_879,c_840,c_76,c_75,c_7,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.00  
% 3.37/1.00  ------  iProver source info
% 3.37/1.00  
% 3.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.00  git: non_committed_changes: false
% 3.37/1.00  git: last_make_outside_of_git: false
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    --mode clausify
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         false
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     num_symb
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       true
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     false
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   []
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_full_bw                           [BwDemod]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  ------ Parsing...
% 3.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  ------ Proving...
% 3.37/1.00  ------ Problem Properties 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  clauses                                 24
% 3.37/1.00  conjectures                             2
% 3.37/1.00  EPR                                     3
% 3.37/1.00  Horn                                    21
% 3.37/1.00  unary                                   14
% 3.37/1.00  binary                                  2
% 3.37/1.00  lits                                    56
% 3.37/1.00  lits eq                                 21
% 3.37/1.00  fd_pure                                 0
% 3.37/1.00  fd_pseudo                               0
% 3.37/1.00  fd_cond                                 1
% 3.37/1.00  fd_pseudo_cond                          4
% 3.37/1.00  AC symbols                              0
% 3.37/1.00  
% 3.37/1.00  ------ Schedule dynamic 5 is on 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  Current options:
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    --mode clausify
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         false
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     none
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       false
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     false
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   []
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_full_bw                           [BwDemod]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS status Theorem for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  fof(f5,axiom,(
% 3.37/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f40,plain,(
% 3.37/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.37/1.00    inference(cnf_transformation,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f7,axiom,(
% 3.37/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f14,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f7])).
% 3.37/1.00  
% 3.37/1.00  fof(f15,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.00    inference(flattening,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f22,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f15])).
% 3.37/1.00  
% 3.37/1.00  fof(f23,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.00    inference(rectify,[],[f22])).
% 3.37/1.00  
% 3.37/1.00  fof(f26,plain,(
% 3.37/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f25,plain,(
% 3.37/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f24,plain,(
% 3.37/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f27,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 3.37/1.00  
% 3.37/1.00  fof(f46,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f41,plain,(
% 3.37/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.37/1.00    inference(cnf_transformation,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f6,axiom,(
% 3.37/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f13,plain,(
% 3.37/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f6])).
% 3.37/1.00  
% 3.37/1.00  fof(f42,plain,(
% 3.37/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f13])).
% 3.37/1.00  
% 3.37/1.00  fof(f4,axiom,(
% 3.37/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f12,plain,(
% 3.37/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f4])).
% 3.37/1.00  
% 3.37/1.00  fof(f39,plain,(
% 3.37/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f12])).
% 3.37/1.00  
% 3.37/1.00  fof(f1,axiom,(
% 3.37/1.00    v1_xboole_0(k1_xboole_0)),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f34,plain,(
% 3.37/1.00    v1_xboole_0(k1_xboole_0)),
% 3.37/1.00    inference(cnf_transformation,[],[f1])).
% 3.37/1.00  
% 3.37/1.00  fof(f2,axiom,(
% 3.37/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f20,plain,(
% 3.37/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.37/1.00    inference(nnf_transformation,[],[f2])).
% 3.37/1.00  
% 3.37/1.00  fof(f21,plain,(
% 3.37/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.37/1.00    inference(flattening,[],[f20])).
% 3.37/1.00  
% 3.37/1.00  fof(f37,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.37/1.00    inference(cnf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f59,plain,(
% 3.37/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f37])).
% 3.37/1.00  
% 3.37/1.00  fof(f3,axiom,(
% 3.37/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f38,plain,(
% 3.37/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f3])).
% 3.37/1.00  
% 3.37/1.00  fof(f9,axiom,(
% 3.37/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f17,plain,(
% 3.37/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.37/1.00    inference(ennf_transformation,[],[f9])).
% 3.37/1.00  
% 3.37/1.00  fof(f30,plain,(
% 3.37/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f31,plain,(
% 3.37/1.00    ! [X0] : (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f56,plain,(
% 3.37/1.00    ( ! [X2,X0] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f45,plain,(
% 3.37/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f61,plain,(
% 3.37/1.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f62,plain,(
% 3.37/1.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f61])).
% 3.37/1.00  
% 3.37/1.00  fof(f55,plain,(
% 3.37/1.00    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 3.37/1.00    inference(cnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f53,plain,(
% 3.37/1.00    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f54,plain,(
% 3.37/1.00    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f8,axiom,(
% 3.37/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f16,plain,(
% 3.37/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.37/1.00    inference(ennf_transformation,[],[f8])).
% 3.37/1.00  
% 3.37/1.00  fof(f28,plain,(
% 3.37/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f29,plain,(
% 3.37/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f28])).
% 3.37/1.00  
% 3.37/1.00  fof(f51,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f10,conjecture,(
% 3.37/1.00    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f11,negated_conjecture,(
% 3.37/1.00    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.37/1.00    inference(negated_conjecture,[],[f10])).
% 3.37/1.00  
% 3.37/1.00  fof(f18,plain,(
% 3.37/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 3.37/1.00    inference(ennf_transformation,[],[f11])).
% 3.37/1.00  
% 3.37/1.00  fof(f19,plain,(
% 3.37/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.37/1.00    inference(flattening,[],[f18])).
% 3.37/1.00  
% 3.37/1.00  fof(f32,plain,(
% 3.37/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f33,plain,(
% 3.37/1.00    k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f32])).
% 3.37/1.00  
% 3.37/1.00  fof(f57,plain,(
% 3.37/1.00    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f33])).
% 3.37/1.00  
% 3.37/1.00  fof(f49,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f50,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f43,plain,(
% 3.37/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f64,plain,(
% 3.37/1.00    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f43])).
% 3.37/1.00  
% 3.37/1.00  fof(f52,plain,(
% 3.37/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f58,plain,(
% 3.37/1.00    k1_xboole_0 != sK5),
% 3.37/1.00    inference(cnf_transformation,[],[f33])).
% 3.37/1.00  
% 3.37/1.00  fof(f35,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f36,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.37/1.00    inference(cnf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f60,plain,(
% 3.37/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.37/1.00    inference(equality_resolution,[],[f36])).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7,plain,
% 3.37/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11,plain,
% 3.37/1.00      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.37/1.00      | r2_hidden(sK0(X0,X1),X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ v1_relat_1(X0)
% 3.37/1.00      | k2_relat_1(X0) = X1 ),
% 3.37/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_636,plain,
% 3.37/1.00      ( k2_relat_1(X0) = X1
% 3.37/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.37/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.37/1.00      | v1_funct_1(X0) != iProver_top
% 3.37/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2008,plain,
% 3.37/1.00      ( k2_relat_1(k1_xboole_0) = X0
% 3.37/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.37/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.37/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.37/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_7,c_636]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6,plain,
% 3.37/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2104,plain,
% 3.37/1.00      ( k1_xboole_0 = X0
% 3.37/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.37/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.37/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.37/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_2008,c_6]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8,plain,
% 3.37/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_66,plain,
% 3.37/1.00      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_68,plain,
% 3.37/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top
% 3.37/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_66]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5,plain,
% 3.37/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_69,plain,
% 3.37/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_71,plain,
% 3.37/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.37/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_69]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_0,plain,
% 3.37/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_77,plain,
% 3.37/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2880,plain,
% 3.37/1.00      ( k1_xboole_0 = X0
% 3.37/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.37/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2104,c_68,c_71,c_77]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1,plain,
% 3.37/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4,plain,
% 3.37/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_639,plain,
% 3.37/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1463,plain,
% 3.37/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1,c_639]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2887,plain,
% 3.37/1.01      ( k1_xboole_0 = X0
% 3.37/1.01      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.37/1.01      inference(forward_subsumption_resolution,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_2880,c_1463]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_19,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1),X0) = np__1 ),
% 3.37/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_629,plain,
% 3.37/1.01      ( k1_funct_1(sK4(X0),X1) = np__1
% 3.37/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2890,plain,
% 3.37/1.01      ( k1_funct_1(sK4(X0),sK0(k1_xboole_0,X0)) = np__1
% 3.37/1.01      | k1_xboole_0 = X0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_2887,c_629]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_12,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.37/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X1) ),
% 3.37/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_635,plain,
% 3.37/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.37/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4187,plain,
% 3.37/1.01      ( k1_xboole_0 = X0
% 3.37/1.01      | r2_hidden(sK0(k1_xboole_0,X0),k1_relat_1(sK4(X0))) != iProver_top
% 3.37/1.01      | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top
% 3.37/1.01      | v1_funct_1(sK4(X0)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK4(X0)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_2890,c_635]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_20,plain,
% 3.37/1.01      ( k1_relat_1(sK4(X0)) = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4193,plain,
% 3.37/1.01      ( k1_xboole_0 = X0
% 3.37/1.01      | r2_hidden(sK0(k1_xboole_0,X0),X0) != iProver_top
% 3.37/1.01      | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top
% 3.37/1.01      | v1_funct_1(sK4(X0)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK4(X0)) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4187,c_20]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_22,plain,
% 3.37/1.01      ( v1_relat_1(sK4(X0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_28,plain,
% 3.37/1.01      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_21,plain,
% 3.37/1.01      ( v1_funct_1(sK4(X0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_31,plain,
% 3.37/1.01      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4217,plain,
% 3.37/1.01      ( k1_xboole_0 = X0
% 3.37/1.01      | r2_hidden(np__1,k2_relat_1(sK4(X0))) = iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4193,c_28,c_31,c_2887]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_16,plain,
% 3.37/1.01      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_24,negated_conjecture,
% 3.37/1.01      ( ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X1)
% 3.37/1.01      | X0 = X1
% 3.37/1.01      | k1_relat_1(X1) != sK5
% 3.37/1.01      | k1_relat_1(X0) != sK5 ),
% 3.37/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_626,plain,
% 3.37/1.01      ( X0 = X1
% 3.37/1.01      | k1_relat_1(X1) != sK5
% 3.37/1.01      | k1_relat_1(X0) != sK5
% 3.37/1.01      | v1_funct_1(X0) != iProver_top
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X0) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_944,plain,
% 3.37/1.01      ( sK3(X0,X1) = X2
% 3.37/1.01      | k1_relat_1(X2) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X2) != iProver_top
% 3.37/1.01      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.37/1.01      | v1_relat_1(X2) != iProver_top
% 3.37/1.01      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_16,c_626]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_18,plain,
% 3.37/1.01      ( v1_relat_1(sK3(X0,X1)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_38,plain,
% 3.37/1.01      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_17,plain,
% 3.37/1.01      ( v1_funct_1(sK3(X0,X1)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_41,plain,
% 3.37/1.01      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1100,plain,
% 3.37/1.01      ( v1_relat_1(X2) != iProver_top
% 3.37/1.01      | sK3(X0,X1) = X2
% 3.37/1.01      | k1_relat_1(X2) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_944,c_38,c_41]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1101,plain,
% 3.37/1.01      ( sK3(X0,X1) = X2
% 3.37/1.01      | k1_relat_1(X2) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X2) != iProver_top
% 3.37/1.01      | v1_relat_1(X2) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_1100]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1111,plain,
% 3.37/1.01      ( sK3(X0,X1) = sK4(X2)
% 3.37/1.01      | sK5 != X2
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(sK4(X2)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK4(X2)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_20,c_1101]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_941,plain,
% 3.37/1.01      ( sK4(X0) = X1
% 3.37/1.01      | k1_relat_1(X1) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_funct_1(sK4(X0)) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(sK4(X0)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_20,c_626]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1039,plain,
% 3.37/1.01      ( v1_relat_1(X1) != iProver_top
% 3.37/1.01      | sK4(X0) = X1
% 3.37/1.01      | k1_relat_1(X1) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_941,c_28,c_31]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1040,plain,
% 3.37/1.01      ( sK4(X0) = X1
% 3.37/1.01      | k1_relat_1(X1) != sK5
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_1039]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1049,plain,
% 3.37/1.01      ( sK3(X0,X1) = sK4(X2)
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | sK5 != X2
% 3.37/1.01      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_16,c_1040]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1071,plain,
% 3.37/1.01      ( ~ v1_funct_1(sK3(X0,X1))
% 3.37/1.01      | ~ v1_relat_1(sK3(X0,X1))
% 3.37/1.01      | sK3(X0,X1) = sK4(X2)
% 3.37/1.01      | sK5 != X0
% 3.37/1.01      | sK5 != X2 ),
% 3.37/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1049]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1224,plain,
% 3.37/1.01      ( sK3(X0,X1) = sK4(X2) | sK5 != X2 | sK5 != X0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1111,c_18,c_17,c_1071]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1225,plain,
% 3.37/1.01      ( sK3(X0,X1) = sK4(X2) | sK5 != X0 | sK5 != X2 ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_1224]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1229,plain,
% 3.37/1.01      ( sK3(sK5,X0) = sK4(X1) | sK5 != X1 ),
% 3.37/1.01      inference(equality_resolution,[status(thm)],[c_1225]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1279,plain,
% 3.37/1.01      ( sK3(sK5,X0) = sK4(sK5) ),
% 3.37/1.01      inference(equality_resolution,[status(thm)],[c_1229]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_14,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.37/1.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X1) ),
% 3.37/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_633,plain,
% 3.37/1.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.37/1.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1778,plain,
% 3.37/1.01      ( r2_hidden(X0,k2_relat_1(sK3(X1,X2))) != iProver_top
% 3.37/1.01      | r2_hidden(sK2(sK3(X1,X2),X0),X1) = iProver_top
% 3.37/1.01      | v1_funct_1(sK3(X1,X2)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK3(X1,X2)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_16,c_633]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_630,plain,
% 3.37/1.01      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_631,plain,
% 3.37/1.01      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3154,plain,
% 3.37/1.01      ( r2_hidden(X0,k2_relat_1(sK3(X1,X2))) != iProver_top
% 3.37/1.01      | r2_hidden(sK2(sK3(X1,X2),X0),X1) = iProver_top ),
% 3.37/1.01      inference(forward_subsumption_resolution,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1778,c_630,c_631]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_15,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1,X2),X0) = X2 ),
% 3.37/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_632,plain,
% 3.37/1.01      ( k1_funct_1(sK3(X0,X1),X2) = X1
% 3.37/1.01      | r2_hidden(X2,X0) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3160,plain,
% 3.37/1.01      ( k1_funct_1(sK3(X0,X1),sK2(sK3(X0,X2),X3)) = X1
% 3.37/1.01      | r2_hidden(X3,k2_relat_1(sK3(X0,X2))) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_3154,c_632]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4412,plain,
% 3.37/1.01      ( k1_funct_1(sK3(sK5,X0),sK2(sK3(sK5,X1),X2)) = X0
% 3.37/1.01      | r2_hidden(X2,k2_relat_1(sK4(sK5))) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1279,c_3160]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4415,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK3(sK5,X0),X1)) = X2
% 3.37/1.01      | r2_hidden(X1,k2_relat_1(sK4(sK5))) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4412,c_1279]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4416,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),X0)) = X1
% 3.37/1.01      | r2_hidden(X0,k2_relat_1(sK4(sK5))) != iProver_top ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_4415,c_1279]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4582,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = X0
% 3.37/1.01      | sK5 = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_4217,c_4416]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_23,negated_conjecture,
% 3.37/1.01      ( k1_xboole_0 != sK5 ),
% 3.37/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3,plain,
% 3.37/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.37/1.01      | k1_xboole_0 = X1
% 3.37/1.01      | k1_xboole_0 = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_75,plain,
% 3.37/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.37/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2,plain,
% 3.37/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_76,plain,
% 3.37/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_340,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_804,plain,
% 3.37/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_340]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_805,plain,
% 3.37/1.01      ( sK5 != k1_xboole_0
% 3.37/1.01      | k1_xboole_0 = sK5
% 3.37/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5026,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = X0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4582,c_23,c_75,c_76,c_805]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5081,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = sK4(sK5) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5026,c_1279]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5114,plain,
% 3.37/1.01      ( k1_funct_1(sK4(sK5),sK2(sK4(sK5),np__1)) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5026,c_2]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_7917,plain,
% 3.37/1.01      ( sK4(sK5) = k1_xboole_0 ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_5081,c_5114]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3035,plain,
% 3.37/1.01      ( k1_relat_1(X0) != X1
% 3.37/1.01      | k1_xboole_0 != X1
% 3.37/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_340]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3036,plain,
% 3.37/1.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.37/1.01      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.37/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_3035]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_345,plain,
% 3.37/1.01      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.37/1.01      theory(equality) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1374,plain,
% 3.37/1.01      ( sK4(sK5) != X0 | k1_relat_1(sK4(sK5)) = k1_relat_1(X0) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_345]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1376,plain,
% 3.37/1.01      ( sK4(sK5) != k1_xboole_0
% 3.37/1.01      | k1_relat_1(sK4(sK5)) = k1_relat_1(k1_xboole_0) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1374]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1161,plain,
% 3.37/1.01      ( k1_relat_1(sK4(sK5)) != X0
% 3.37/1.01      | k1_xboole_0 != X0
% 3.37/1.01      | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_340]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1373,plain,
% 3.37/1.01      ( k1_relat_1(sK4(sK5)) != k1_relat_1(X0)
% 3.37/1.01      | k1_xboole_0 != k1_relat_1(X0)
% 3.37/1.01      | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1161]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1375,plain,
% 3.37/1.01      ( k1_relat_1(sK4(sK5)) != k1_relat_1(k1_xboole_0)
% 3.37/1.01      | k1_xboole_0 = k1_relat_1(sK4(sK5))
% 3.37/1.01      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1373]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_964,plain,
% 3.37/1.01      ( sK5 != k1_relat_1(sK4(sK5))
% 3.37/1.01      | k1_xboole_0 != k1_relat_1(sK4(sK5))
% 3.37/1.01      | k1_xboole_0 = sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_880,plain,
% 3.37/1.01      ( k1_relat_1(sK4(sK5)) = sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_823,plain,
% 3.37/1.01      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_340]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_839,plain,
% 3.37/1.01      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_823]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_879,plain,
% 3.37/1.01      ( k1_relat_1(sK4(sK5)) != sK5
% 3.37/1.01      | sK5 = k1_relat_1(sK4(sK5))
% 3.37/1.01      | sK5 != sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_839]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_339,plain,( X0 = X0 ),theory(equality) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_840,plain,
% 3.37/1.01      ( sK5 = sK5 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_339]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(contradiction,plain,
% 3.37/1.01      ( $false ),
% 3.37/1.01      inference(minisat,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_7917,c_3036,c_1376,c_1375,c_964,c_880,c_879,c_840,
% 3.37/1.01                 c_76,c_75,c_7,c_23]) ).
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  ------                               Statistics
% 3.37/1.01  
% 3.37/1.01  ------ General
% 3.37/1.01  
% 3.37/1.01  abstr_ref_over_cycles:                  0
% 3.37/1.01  abstr_ref_under_cycles:                 0
% 3.37/1.01  gc_basic_clause_elim:                   0
% 3.37/1.01  forced_gc_time:                         0
% 3.37/1.01  parsing_time:                           0.009
% 3.37/1.01  unif_index_cands_time:                  0.
% 3.37/1.01  unif_index_add_time:                    0.
% 3.37/1.01  orderings_time:                         0.
% 3.37/1.01  out_proof_time:                         0.009
% 3.37/1.01  total_time:                             0.332
% 3.37/1.01  num_of_symbols:                         47
% 3.37/1.01  num_of_terms:                           7832
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing
% 3.37/1.01  
% 3.37/1.01  num_of_splits:                          0
% 3.37/1.01  num_of_split_atoms:                     0
% 3.37/1.01  num_of_reused_defs:                     0
% 3.37/1.01  num_eq_ax_congr_red:                    27
% 3.37/1.01  num_of_sem_filtered_clauses:            1
% 3.37/1.01  num_of_subtypes:                        0
% 3.37/1.01  monotx_restored_types:                  0
% 3.37/1.01  sat_num_of_epr_types:                   0
% 3.37/1.01  sat_num_of_non_cyclic_types:            0
% 3.37/1.01  sat_guarded_non_collapsed_types:        0
% 3.37/1.01  num_pure_diseq_elim:                    0
% 3.37/1.01  simp_replaced_by:                       0
% 3.37/1.01  res_preprocessed:                       116
% 3.37/1.01  prep_upred:                             0
% 3.37/1.01  prep_unflattend:                        2
% 3.37/1.01  smt_new_axioms:                         0
% 3.37/1.01  pred_elim_cands:                        3
% 3.37/1.01  pred_elim:                              1
% 3.37/1.01  pred_elim_cl:                           1
% 3.37/1.01  pred_elim_cycles:                       3
% 3.37/1.01  merged_defs:                            0
% 3.37/1.01  merged_defs_ncl:                        0
% 3.37/1.01  bin_hyper_res:                          0
% 3.37/1.01  prep_cycles:                            4
% 3.37/1.01  pred_elim_time:                         0.001
% 3.37/1.01  splitting_time:                         0.
% 3.37/1.01  sem_filter_time:                        0.
% 3.37/1.01  monotx_time:                            0.005
% 3.37/1.01  subtype_inf_time:                       0.
% 3.37/1.01  
% 3.37/1.01  ------ Problem properties
% 3.37/1.01  
% 3.37/1.01  clauses:                                24
% 3.37/1.01  conjectures:                            2
% 3.37/1.01  epr:                                    3
% 3.37/1.01  horn:                                   21
% 3.37/1.01  ground:                                 5
% 3.37/1.01  unary:                                  14
% 3.37/1.01  binary:                                 2
% 3.37/1.01  lits:                                   56
% 3.37/1.01  lits_eq:                                21
% 3.37/1.01  fd_pure:                                0
% 3.37/1.01  fd_pseudo:                              0
% 3.37/1.01  fd_cond:                                1
% 3.37/1.01  fd_pseudo_cond:                         4
% 3.37/1.01  ac_symbols:                             0
% 3.37/1.01  
% 3.37/1.01  ------ Propositional Solver
% 3.37/1.01  
% 3.37/1.01  prop_solver_calls:                      30
% 3.37/1.01  prop_fast_solver_calls:                 788
% 3.37/1.01  smt_solver_calls:                       0
% 3.37/1.01  smt_fast_solver_calls:                  0
% 3.37/1.01  prop_num_of_clauses:                    2049
% 3.37/1.01  prop_preprocess_simplified:             5460
% 3.37/1.01  prop_fo_subsumed:                       31
% 3.37/1.01  prop_solver_time:                       0.
% 3.37/1.01  smt_solver_time:                        0.
% 3.37/1.01  smt_fast_solver_time:                   0.
% 3.37/1.01  prop_fast_solver_time:                  0.
% 3.37/1.01  prop_unsat_core_time:                   0.
% 3.37/1.01  
% 3.37/1.01  ------ QBF
% 3.37/1.01  
% 3.37/1.01  qbf_q_res:                              0
% 3.37/1.01  qbf_num_tautologies:                    0
% 3.37/1.01  qbf_prep_cycles:                        0
% 3.37/1.01  
% 3.37/1.01  ------ BMC1
% 3.37/1.01  
% 3.37/1.01  bmc1_current_bound:                     -1
% 3.37/1.01  bmc1_last_solved_bound:                 -1
% 3.37/1.01  bmc1_unsat_core_size:                   -1
% 3.37/1.01  bmc1_unsat_core_parents_size:           -1
% 3.37/1.01  bmc1_merge_next_fun:                    0
% 3.37/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation
% 3.37/1.01  
% 3.37/1.01  inst_num_of_clauses:                    664
% 3.37/1.01  inst_num_in_passive:                    275
% 3.37/1.01  inst_num_in_active:                     303
% 3.37/1.01  inst_num_in_unprocessed:                86
% 3.37/1.01  inst_num_of_loops:                      330
% 3.37/1.01  inst_num_of_learning_restarts:          0
% 3.37/1.01  inst_num_moves_active_passive:          21
% 3.37/1.01  inst_lit_activity:                      0
% 3.37/1.01  inst_lit_activity_moves:                0
% 3.37/1.01  inst_num_tautologies:                   0
% 3.37/1.01  inst_num_prop_implied:                  0
% 3.37/1.01  inst_num_existing_simplified:           0
% 3.37/1.01  inst_num_eq_res_simplified:             0
% 3.37/1.01  inst_num_child_elim:                    0
% 3.37/1.01  inst_num_of_dismatching_blockings:      103
% 3.37/1.01  inst_num_of_non_proper_insts:           595
% 3.37/1.01  inst_num_of_duplicates:                 0
% 3.37/1.01  inst_inst_num_from_inst_to_res:         0
% 3.37/1.01  inst_dismatching_checking_time:         0.
% 3.37/1.01  
% 3.37/1.01  ------ Resolution
% 3.37/1.01  
% 3.37/1.01  res_num_of_clauses:                     0
% 3.37/1.01  res_num_in_passive:                     0
% 3.37/1.01  res_num_in_active:                      0
% 3.37/1.01  res_num_of_loops:                       120
% 3.37/1.01  res_forward_subset_subsumed:            39
% 3.37/1.01  res_backward_subset_subsumed:           0
% 3.37/1.01  res_forward_subsumed:                   0
% 3.37/1.01  res_backward_subsumed:                  0
% 3.37/1.01  res_forward_subsumption_resolution:     0
% 3.37/1.01  res_backward_subsumption_resolution:    0
% 3.37/1.01  res_clause_to_clause_subsumption:       915
% 3.37/1.01  res_orphan_elimination:                 0
% 3.37/1.01  res_tautology_del:                      32
% 3.37/1.01  res_num_eq_res_simplified:              0
% 3.37/1.01  res_num_sel_changes:                    0
% 3.37/1.01  res_moves_from_active_to_pass:          0
% 3.37/1.01  
% 3.37/1.01  ------ Superposition
% 3.37/1.01  
% 3.37/1.01  sup_time_total:                         0.
% 3.37/1.01  sup_time_generating:                    0.
% 3.37/1.01  sup_time_sim_full:                      0.
% 3.37/1.01  sup_time_sim_immed:                     0.
% 3.37/1.01  
% 3.37/1.01  sup_num_of_clauses:                     201
% 3.37/1.01  sup_num_in_active:                      43
% 3.37/1.01  sup_num_in_passive:                     158
% 3.37/1.01  sup_num_of_loops:                       65
% 3.37/1.01  sup_fw_superposition:                   156
% 3.37/1.01  sup_bw_superposition:                   207
% 3.37/1.01  sup_immediate_simplified:               58
% 3.37/1.01  sup_given_eliminated:                   6
% 3.37/1.01  comparisons_done:                       0
% 3.37/1.01  comparisons_avoided:                    6
% 3.37/1.01  
% 3.37/1.01  ------ Simplifications
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  sim_fw_subset_subsumed:                 67
% 3.37/1.01  sim_bw_subset_subsumed:                 10
% 3.37/1.01  sim_fw_subsumed:                        111
% 3.37/1.01  sim_bw_subsumed:                        33
% 3.37/1.01  sim_fw_subsumption_res:                 31
% 3.37/1.01  sim_bw_subsumption_res:                 13
% 3.37/1.01  sim_tautology_del:                      0
% 3.37/1.01  sim_eq_tautology_del:                   7
% 3.37/1.01  sim_eq_res_simp:                        0
% 3.37/1.01  sim_fw_demodulated:                     27
% 3.37/1.01  sim_bw_demodulated:                     188
% 3.37/1.01  sim_light_normalised:                   104
% 3.37/1.01  sim_joinable_taut:                      0
% 3.37/1.01  sim_joinable_simp:                      0
% 3.37/1.01  sim_ac_normalised:                      0
% 3.37/1.01  sim_smt_subsumption:                    0
% 3.37/1.01  
%------------------------------------------------------------------------------
