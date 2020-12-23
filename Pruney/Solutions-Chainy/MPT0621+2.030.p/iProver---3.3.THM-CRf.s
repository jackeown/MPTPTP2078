%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:26 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  190 (2612 expanded)
%              Number of clauses        :  119 ( 999 expanded)
%              Number of leaves         :   22 ( 632 expanded)
%              Depth                    :   35
%              Number of atoms          :  635 (11555 expanded)
%              Number of equality atoms :  382 (5872 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f20,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK5(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK5(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK5(X0)) = X0
      & v1_funct_1(sK5(X0))
      & v1_relat_1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f37,plain,
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
   => ( k1_xboole_0 != sK6
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK6
              | k1_relat_1(X1) != sK6
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k1_xboole_0 != sK6
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK6
            | k1_relat_1(X1) != sK6
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f37])).

fof(f66,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK6
      | k1_relat_1(X1) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X2,X0] :
      ( k1_funct_1(sK5(X0),X2) = np__1
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f71,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

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

fof(f18,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_621,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4817,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_621])).

cnf(c_7,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4946,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4817,c_7])).

cnf(c_22,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_43,plain,
    ( v1_relat_1(sK4(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_42,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_44,plain,
    ( v1_relat_1(sK4(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_21,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_45,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_47,plain,
    ( v1_funct_1(sK4(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_20,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48,plain,
    ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_254,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_827,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(X1))
    | X0 != sK4(X1) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_828,plain,
    ( X0 != sK4(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_830,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0)
    | v1_relat_1(sK4(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_257,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_842,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(X1))
    | X0 != sK4(X1) ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_843,plain,
    ( X0 != sK4(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_845,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0)
    | v1_funct_1(sK4(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_924,plain,
    ( ~ v1_xboole_0(sK4(X0))
    | k1_xboole_0 = sK4(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_928,plain,
    ( ~ v1_xboole_0(sK4(k1_xboole_0))
    | k1_xboole_0 = sK4(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1174,plain,
    ( ~ v1_relat_1(sK4(X0))
    | v1_xboole_0(sK4(X0))
    | ~ v1_xboole_0(k1_relat_1(sK4(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1176,plain,
    ( ~ v1_relat_1(sK4(k1_xboole_0))
    | v1_xboole_0(sK4(k1_xboole_0))
    | ~ v1_xboole_0(k1_relat_1(sK4(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_250,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2004,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK4(X1)))
    | k1_relat_1(sK4(X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_2006,plain,
    ( v1_xboole_0(k1_relat_1(sK4(k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_5164,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4946,c_43,c_44,c_47,c_48,c_0,c_830,c_845,c_928,c_1176,c_2006])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_625,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2702,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_625])).

cnf(c_5171,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5164,c_2702])).

cnf(c_24,plain,
    ( k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != sK6
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_608,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK6
    | k1_relat_1(X0) != sK6
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1091,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_608])).

cnf(c_1268,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK4(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_42,c_45])).

cnf(c_1269,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1268])).

cnf(c_1280,plain,
    ( sK5(X0) = sK4(X1)
    | sK6 != X0
    | sK6 != X1
    | v1_funct_1(sK5(X0)) != iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1269])).

cnf(c_26,plain,
    ( v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1313,plain,
    ( ~ v1_funct_1(sK5(X0))
    | ~ v1_relat_1(sK5(X0))
    | sK5(X0) = sK4(X1)
    | sK6 != X0
    | sK6 != X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1280])).

cnf(c_1593,plain,
    ( sK5(X0) = sK4(X1)
    | sK6 != X0
    | sK6 != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1280,c_26,c_25,c_1313])).

cnf(c_1598,plain,
    ( sK4(X0) = sK5(sK6)
    | sK6 != X0 ),
    inference(equality_resolution,[status(thm)],[c_1593])).

cnf(c_1991,plain,
    ( sK5(sK6) = sK4(sK6) ),
    inference(equality_resolution,[status(thm)],[c_1598])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1),X0) = np__1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_611,plain,
    ( k1_funct_1(sK5(X0),X1) = np__1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5174,plain,
    ( k1_funct_1(sK5(X0),sK0(k1_xboole_0,X0)) = np__1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_5171,c_611])).

cnf(c_6769,plain,
    ( k1_funct_1(sK4(sK6),sK0(k1_xboole_0,sK6)) = np__1
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1991,c_5174])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_87,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_249,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_852,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_853,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_6830,plain,
    ( k1_funct_1(sK4(sK6),sK0(k1_xboole_0,sK6)) = np__1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6769,c_27,c_86,c_87,c_853])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_620,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6834,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),k1_relat_1(sK4(sK6))) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6830,c_620])).

cnf(c_6839,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6834,c_20])).

cnf(c_3406,plain,
    ( v1_funct_1(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3407,plain,
    ( v1_funct_1(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3406])).

cnf(c_6862,plain,
    ( r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6839,c_3407])).

cnf(c_6863,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6862])).

cnf(c_612,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6869,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
    | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6863,c_612])).

cnf(c_6873,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5171,c_6869])).

cnf(c_7052,plain,
    ( r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6873,c_27,c_86,c_87,c_853])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_618,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_614,plain,
    ( k1_funct_1(sK4(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3014,plain,
    ( k1_funct_1(sK4(k1_relat_1(X0)),sK2(X0,X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_614])).

cnf(c_7501,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(sK6))),sK2(sK4(sK6),np__1)) = k1_xboole_0
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7052,c_3014])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_619,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7060,plain,
    ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7052,c_619])).

cnf(c_7348,plain,
    ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7060,c_3407])).

cnf(c_7354,plain,
    ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7348,c_612])).

cnf(c_7506,plain,
    ( np__1 = k1_xboole_0
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7501,c_20,c_7354])).

cnf(c_7403,plain,
    ( v1_relat_1(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_7404,plain,
    ( v1_relat_1(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7403])).

cnf(c_7677,plain,
    ( np__1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7506,c_3407,c_7404])).

cnf(c_7684,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK4(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7677,c_7052])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_617,plain,
    ( k1_funct_1(sK3(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3102,plain,
    ( k1_funct_1(sK3(k1_relat_1(X0),X1),sK2(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_617])).

cnf(c_9657,plain,
    ( k1_funct_1(sK3(k1_relat_1(sK4(sK6)),X0),sK2(sK4(sK6),k1_xboole_0)) = X0
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7684,c_3102])).

cnf(c_16,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1188,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_608])).

cnf(c_18,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_52,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_55,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1501,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1188,c_52,c_55])).

cnf(c_1502,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1501])).

cnf(c_1512,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK6 != X2
    | sK6 != X0
    | v1_funct_1(sK4(X2)) != iProver_top
    | v1_relat_1(sK4(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1502])).

cnf(c_1278,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK6 != X0
    | sK6 != X2
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1269])).

cnf(c_1311,plain,
    ( ~ v1_funct_1(sK3(X0,X1))
    | ~ v1_relat_1(sK3(X0,X1))
    | sK3(X0,X1) = sK4(X2)
    | sK6 != X0
    | sK6 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1278])).

cnf(c_1656,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK6 != X2
    | sK6 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1512,c_18,c_17,c_1311])).

cnf(c_1657,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK6 != X0
    | sK6 != X2 ),
    inference(renaming,[status(thm)],[c_1656])).

cnf(c_1661,plain,
    ( sK3(sK6,X0) = sK4(X1)
    | sK6 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1657])).

cnf(c_2226,plain,
    ( sK3(sK6,X0) = sK4(sK6) ),
    inference(equality_resolution,[status(thm)],[c_1661])).

cnf(c_7680,plain,
    ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7677,c_7354])).

cnf(c_9685,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK4(sK6)) != iProver_top
    | v1_relat_1(sK4(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9657,c_20,c_2226,c_7680])).

cnf(c_9878,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9685,c_3407,c_7404])).

cnf(c_820,plain,
    ( k1_relat_1(X0) != sK6
    | sK6 != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_608])).

cnf(c_855,plain,
    ( sK6 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_27,c_86,c_87,c_853])).

cnf(c_9964,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9878,c_855])).

cnf(c_9966,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9964])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:40:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.35/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.99  
% 3.35/0.99  ------  iProver source info
% 3.35/0.99  
% 3.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.99  git: non_committed_changes: false
% 3.35/0.99  git: last_make_outside_of_git: false
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     num_symb
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       true
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  ------ Parsing...
% 3.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.99  ------ Proving...
% 3.35/0.99  ------ Problem Properties 
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  clauses                                 29
% 3.35/0.99  conjectures                             2
% 3.35/0.99  EPR                                     3
% 3.35/0.99  Horn                                    26
% 3.35/0.99  unary                                   16
% 3.35/0.99  binary                                  4
% 3.35/0.99  lits                                    65
% 3.35/0.99  lits eq                                 24
% 3.35/0.99  fd_pure                                 0
% 3.35/0.99  fd_pseudo                               0
% 3.35/0.99  fd_cond                                 2
% 3.35/0.99  fd_pseudo_cond                          4
% 3.35/0.99  AC symbols                              0
% 3.35/0.99  
% 3.35/0.99  ------ Schedule dynamic 5 is on 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  Current options:
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     none
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       false
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ Proving...
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS status Theorem for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99   Resolution empty clause
% 3.35/0.99  
% 3.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  fof(f6,axiom,(
% 3.35/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f46,plain,(
% 3.35/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.35/0.99    inference(cnf_transformation,[],[f6])).
% 3.35/0.99  
% 3.35/0.99  fof(f7,axiom,(
% 3.35/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f16,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f7])).
% 3.35/0.99  
% 3.35/0.99  fof(f17,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(flattening,[],[f16])).
% 3.35/0.99  
% 3.35/0.99  fof(f25,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f17])).
% 3.35/0.99  
% 3.35/0.99  fof(f26,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(rectify,[],[f25])).
% 3.35/0.99  
% 3.35/0.99  fof(f29,plain,(
% 3.35/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f28,plain,(
% 3.35/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f27,plain,(
% 3.35/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f30,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 3.35/0.99  
% 3.35/0.99  fof(f51,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f47,plain,(
% 3.35/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.35/0.99    inference(cnf_transformation,[],[f6])).
% 3.35/0.99  
% 3.35/0.99  fof(f9,axiom,(
% 3.35/0.99    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f19,plain,(
% 3.35/0.99    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.35/0.99    inference(ennf_transformation,[],[f9])).
% 3.35/0.99  
% 3.35/0.99  fof(f33,plain,(
% 3.35/0.99    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f34,plain,(
% 3.35/0.99    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f58,plain,(
% 3.35/0.99    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f59,plain,(
% 3.35/0.99    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f60,plain,(
% 3.35/0.99    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 3.35/0.99    inference(cnf_transformation,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f1,axiom,(
% 3.35/0.99    v1_xboole_0(k1_xboole_0)),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f39,plain,(
% 3.35/0.99    v1_xboole_0(k1_xboole_0)),
% 3.35/0.99    inference(cnf_transformation,[],[f1])).
% 3.35/0.99  
% 3.35/0.99  fof(f2,axiom,(
% 3.35/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f13,plain,(
% 3.35/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f2])).
% 3.35/0.99  
% 3.35/0.99  fof(f40,plain,(
% 3.35/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f13])).
% 3.35/0.99  
% 3.35/0.99  fof(f5,axiom,(
% 3.35/0.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f14,plain,(
% 3.35/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f5])).
% 3.35/0.99  
% 3.35/0.99  fof(f15,plain,(
% 3.35/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.35/0.99    inference(flattening,[],[f14])).
% 3.35/0.99  
% 3.35/0.99  fof(f45,plain,(
% 3.35/0.99    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f15])).
% 3.35/0.99  
% 3.35/0.99  fof(f3,axiom,(
% 3.35/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f23,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(nnf_transformation,[],[f3])).
% 3.35/0.99  
% 3.35/0.99  fof(f24,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(flattening,[],[f23])).
% 3.35/0.99  
% 3.35/0.99  fof(f43,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f68,plain,(
% 3.35/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f43])).
% 3.35/0.99  
% 3.35/0.99  fof(f4,axiom,(
% 3.35/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f44,plain,(
% 3.35/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f4])).
% 3.35/0.99  
% 3.35/0.99  fof(f10,axiom,(
% 3.35/0.99    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f20,plain,(
% 3.35/0.99    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.35/0.99    inference(ennf_transformation,[],[f10])).
% 3.35/0.99  
% 3.35/0.99  fof(f35,plain,(
% 3.35/0.99    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK5(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f36,plain,(
% 3.35/0.99    ! [X0] : (! [X2] : (k1_funct_1(sK5(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).
% 3.35/0.99  
% 3.35/0.99  fof(f64,plain,(
% 3.35/0.99    ( ! [X0] : (k1_relat_1(sK5(X0)) = X0) )),
% 3.35/0.99    inference(cnf_transformation,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f11,conjecture,(
% 3.35/0.99    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f12,negated_conjecture,(
% 3.35/0.99    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.35/0.99    inference(negated_conjecture,[],[f11])).
% 3.35/0.99  
% 3.35/0.99  fof(f21,plain,(
% 3.35/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f12])).
% 3.35/0.99  
% 3.35/0.99  fof(f22,plain,(
% 3.35/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.35/0.99    inference(flattening,[],[f21])).
% 3.35/0.99  
% 3.35/0.99  fof(f37,plain,(
% 3.35/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK6 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f38,plain,(
% 3.35/0.99    k1_xboole_0 != sK6 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f37])).
% 3.35/0.99  
% 3.35/0.99  fof(f66,plain,(
% 3.35/0.99    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f38])).
% 3.35/0.99  
% 3.35/0.99  fof(f62,plain,(
% 3.35/0.99    ( ! [X0] : (v1_relat_1(sK5(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f63,plain,(
% 3.35/0.99    ( ! [X0] : (v1_funct_1(sK5(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f65,plain,(
% 3.35/0.99    ( ! [X2,X0] : (k1_funct_1(sK5(X0),X2) = np__1 | ~r2_hidden(X2,X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f67,plain,(
% 3.35/0.99    k1_xboole_0 != sK6),
% 3.35/0.99    inference(cnf_transformation,[],[f38])).
% 3.35/0.99  
% 3.35/0.99  fof(f41,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f42,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f69,plain,(
% 3.35/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.35/0.99    inference(equality_resolution,[],[f42])).
% 3.35/0.99  
% 3.35/0.99  fof(f50,plain,(
% 3.35/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f70,plain,(
% 3.35/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f50])).
% 3.35/0.99  
% 3.35/0.99  fof(f71,plain,(
% 3.35/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f70])).
% 3.35/0.99  
% 3.35/0.99  fof(f48,plain,(
% 3.35/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f73,plain,(
% 3.35/0.99    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f61,plain,(
% 3.35/0.99    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f49,plain,(
% 3.35/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f72,plain,(
% 3.35/0.99    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f49])).
% 3.35/0.99  
% 3.35/0.99  fof(f8,axiom,(
% 3.35/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f18,plain,(
% 3.35/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.35/0.99    inference(ennf_transformation,[],[f8])).
% 3.35/0.99  
% 3.35/0.99  fof(f31,plain,(
% 3.35/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f32,plain,(
% 3.35/0.99    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).
% 3.35/0.99  
% 3.35/0.99  fof(f57,plain,(
% 3.35/0.99    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f56,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 3.35/0.99    inference(cnf_transformation,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f54,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f55,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8,plain,
% 3.35/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_11,plain,
% 3.35/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.35/0.99      | r2_hidden(sK0(X0,X1),X1)
% 3.35/0.99      | ~ v1_funct_1(X0)
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | k2_relat_1(X0) = X1 ),
% 3.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_621,plain,
% 3.35/0.99      ( k2_relat_1(X0) = X1
% 3.35/0.99      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.35/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4817,plain,
% 3.35/0.99      ( k2_relat_1(k1_xboole_0) = X0
% 3.35/0.99      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.35/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.35/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.35/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_8,c_621]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7,plain,
% 3.35/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4946,plain,
% 3.35/0.99      ( k1_xboole_0 = X0
% 3.35/0.99      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.35/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.35/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.35/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_4817,c_7]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_22,plain,
% 3.35/0.99      ( v1_relat_1(sK4(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_43,plain,
% 3.35/0.99      ( v1_relat_1(sK4(k1_xboole_0)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_42,plain,
% 3.35/0.99      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_44,plain,
% 3.35/0.99      ( v1_relat_1(sK4(k1_xboole_0)) = iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_21,plain,
% 3.35/0.99      ( v1_funct_1(sK4(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_45,plain,
% 3.35/0.99      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_47,plain,
% 3.35/0.99      ( v1_funct_1(sK4(k1_xboole_0)) = iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_45]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_20,plain,
% 3.35/0.99      ( k1_relat_1(sK4(X0)) = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_48,plain,
% 3.35/0.99      ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_0,plain,
% 3.35/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_254,plain,
% 3.35/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_827,plain,
% 3.35/0.99      ( v1_relat_1(X0) | ~ v1_relat_1(sK4(X1)) | X0 != sK4(X1) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_254]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_828,plain,
% 3.35/0.99      ( X0 != sK4(X1)
% 3.35/0.99      | v1_relat_1(X0) = iProver_top
% 3.35/0.99      | v1_relat_1(sK4(X1)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_830,plain,
% 3.35/0.99      ( k1_xboole_0 != sK4(k1_xboole_0)
% 3.35/0.99      | v1_relat_1(sK4(k1_xboole_0)) != iProver_top
% 3.35/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_828]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_257,plain,
% 3.35/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_842,plain,
% 3.35/0.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK4(X1)) | X0 != sK4(X1) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_257]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_843,plain,
% 3.35/0.99      ( X0 != sK4(X1)
% 3.35/0.99      | v1_funct_1(X0) = iProver_top
% 3.35/0.99      | v1_funct_1(sK4(X1)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_845,plain,
% 3.35/0.99      ( k1_xboole_0 != sK4(k1_xboole_0)
% 3.35/0.99      | v1_funct_1(sK4(k1_xboole_0)) != iProver_top
% 3.35/0.99      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_843]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_924,plain,
% 3.35/0.99      ( ~ v1_xboole_0(sK4(X0)) | k1_xboole_0 = sK4(X0) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_928,plain,
% 3.35/0.99      ( ~ v1_xboole_0(sK4(k1_xboole_0)) | k1_xboole_0 = sK4(k1_xboole_0) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_924]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6,plain,
% 3.35/0.99      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1174,plain,
% 3.35/0.99      ( ~ v1_relat_1(sK4(X0))
% 3.35/0.99      | v1_xboole_0(sK4(X0))
% 3.35/0.99      | ~ v1_xboole_0(k1_relat_1(sK4(X0))) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1176,plain,
% 3.35/0.99      ( ~ v1_relat_1(sK4(k1_xboole_0))
% 3.35/0.99      | v1_xboole_0(sK4(k1_xboole_0))
% 3.35/0.99      | ~ v1_xboole_0(k1_relat_1(sK4(k1_xboole_0))) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1174]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_250,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2004,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0)
% 3.35/0.99      | v1_xboole_0(k1_relat_1(sK4(X1)))
% 3.35/0.99      | k1_relat_1(sK4(X1)) != X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_250]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2006,plain,
% 3.35/0.99      ( v1_xboole_0(k1_relat_1(sK4(k1_xboole_0)))
% 3.35/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.35/0.99      | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5164,plain,
% 3.35/0.99      ( k1_xboole_0 = X0
% 3.35/0.99      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.35/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_4946,c_43,c_44,c_47,c_48,c_0,c_830,c_845,c_928,c_1176,
% 3.35/0.99                 c_2006]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2,plain,
% 3.35/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_625,plain,
% 3.35/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2702,plain,
% 3.35/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2,c_625]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5171,plain,
% 3.35/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.35/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5164,c_2702]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_24,plain,
% 3.35/0.99      ( k1_relat_1(sK5(X0)) = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_28,negated_conjecture,
% 3.35/0.99      ( ~ v1_funct_1(X0)
% 3.35/0.99      | ~ v1_funct_1(X1)
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | ~ v1_relat_1(X1)
% 3.35/0.99      | X0 = X1
% 3.35/0.99      | k1_relat_1(X1) != sK6
% 3.35/0.99      | k1_relat_1(X0) != sK6 ),
% 3.35/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_608,plain,
% 3.35/0.99      ( X0 = X1
% 3.35/0.99      | k1_relat_1(X1) != sK6
% 3.35/0.99      | k1_relat_1(X0) != sK6
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_funct_1(X1) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1091,plain,
% 3.35/0.99      ( sK4(X0) = X1
% 3.35/0.99      | k1_relat_1(X1) != sK6
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | v1_funct_1(X1) != iProver_top
% 3.35/0.99      | v1_funct_1(sK4(X0)) != iProver_top
% 3.35/0.99      | v1_relat_1(X1) != iProver_top
% 3.35/0.99      | v1_relat_1(sK4(X0)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_20,c_608]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1268,plain,
% 3.35/0.99      ( v1_relat_1(X1) != iProver_top
% 3.35/0.99      | sK4(X0) = X1
% 3.35/0.99      | k1_relat_1(X1) != sK6
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1091,c_42,c_45]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1269,plain,
% 3.35/0.99      ( sK4(X0) = X1
% 3.35/0.99      | k1_relat_1(X1) != sK6
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | v1_funct_1(X1) != iProver_top
% 3.35/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_1268]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1280,plain,
% 3.35/0.99      ( sK5(X0) = sK4(X1)
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | sK6 != X1
% 3.35/0.99      | v1_funct_1(sK5(X0)) != iProver_top
% 3.35/0.99      | v1_relat_1(sK5(X0)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_24,c_1269]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_26,plain,
% 3.35/0.99      ( v1_relat_1(sK5(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_25,plain,
% 3.35/0.99      ( v1_funct_1(sK5(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1313,plain,
% 3.35/0.99      ( ~ v1_funct_1(sK5(X0))
% 3.35/0.99      | ~ v1_relat_1(sK5(X0))
% 3.35/0.99      | sK5(X0) = sK4(X1)
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | sK6 != X1 ),
% 3.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1280]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1593,plain,
% 3.35/0.99      ( sK5(X0) = sK4(X1) | sK6 != X0 | sK6 != X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1280,c_26,c_25,c_1313]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1598,plain,
% 3.35/1.00      ( sK4(X0) = sK5(sK6) | sK6 != X0 ),
% 3.35/1.00      inference(equality_resolution,[status(thm)],[c_1593]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1991,plain,
% 3.35/1.00      ( sK5(sK6) = sK4(sK6) ),
% 3.35/1.00      inference(equality_resolution,[status(thm)],[c_1598]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_23,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1),X0) = np__1 ),
% 3.35/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_611,plain,
% 3.35/1.00      ( k1_funct_1(sK5(X0),X1) = np__1 | r2_hidden(X1,X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5174,plain,
% 3.35/1.00      ( k1_funct_1(sK5(X0),sK0(k1_xboole_0,X0)) = np__1 | k1_xboole_0 = X0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_5171,c_611]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6769,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK0(k1_xboole_0,sK6)) = np__1 | sK6 = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1991,c_5174]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_27,negated_conjecture,
% 3.35/1.00      ( k1_xboole_0 != sK6 ),
% 3.35/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_4,plain,
% 3.35/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.35/1.00      | k1_xboole_0 = X0
% 3.35/1.00      | k1_xboole_0 = X1 ),
% 3.35/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_86,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.35/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_87,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_249,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_852,plain,
% 3.35/1.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_249]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_853,plain,
% 3.35/1.00      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_852]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6830,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK0(k1_xboole_0,sK6)) = np__1 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_6769,c_27,c_86,c_87,c_853]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_12,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.35/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.35/1.00      | ~ v1_funct_1(X1)
% 3.35/1.00      | ~ v1_relat_1(X1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_620,plain,
% 3.35/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.35/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.35/1.00      | v1_funct_1(X1) != iProver_top
% 3.35/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6834,plain,
% 3.35/1.00      ( r2_hidden(sK0(k1_xboole_0,sK6),k1_relat_1(sK4(sK6))) != iProver_top
% 3.35/1.00      | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_6830,c_620]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6839,plain,
% 3.35/1.00      ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
% 3.35/1.00      | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_6834,c_20]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3406,plain,
% 3.35/1.00      ( v1_funct_1(sK4(sK6)) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3407,plain,
% 3.35/1.00      ( v1_funct_1(sK4(sK6)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_3406]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6862,plain,
% 3.35/1.00      ( r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
% 3.35/1.00      | r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6839,c_3407]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6863,plain,
% 3.35/1.00      ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
% 3.35/1.00      | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(renaming,[status(thm)],[c_6862]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_612,plain,
% 3.35/1.00      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6869,plain,
% 3.35/1.00      ( r2_hidden(sK0(k1_xboole_0,sK6),sK6) != iProver_top
% 3.35/1.00      | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
% 3.35/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6863,c_612]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_6873,plain,
% 3.35/1.00      ( sK6 = k1_xboole_0
% 3.35/1.00      | r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_5171,c_6869]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7052,plain,
% 3.35/1.00      ( r2_hidden(np__1,k2_relat_1(sK4(sK6))) = iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_6873,c_27,c_86,c_87,c_853]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_14,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.35/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.35/1.00      | ~ v1_funct_1(X1)
% 3.35/1.00      | ~ v1_relat_1(X1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_618,plain,
% 3.35/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.35/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.35/1.00      | v1_funct_1(X1) != iProver_top
% 3.35/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_19,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1),X0) = k1_xboole_0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_614,plain,
% 3.35/1.00      ( k1_funct_1(sK4(X0),X1) = k1_xboole_0
% 3.35/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3014,plain,
% 3.35/1.00      ( k1_funct_1(sK4(k1_relat_1(X0)),sK2(X0,X1)) = k1_xboole_0
% 3.35/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_618,c_614]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7501,plain,
% 3.35/1.00      ( k1_funct_1(sK4(k1_relat_1(sK4(sK6))),sK2(sK4(sK6),np__1)) = k1_xboole_0
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_7052,c_3014]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_13,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.35/1.00      | ~ v1_funct_1(X1)
% 3.35/1.00      | ~ v1_relat_1(X1)
% 3.35/1.00      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_619,plain,
% 3.35/1.00      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 3.35/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7060,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_7052,c_619]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7348,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7060,c_3407]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7354,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),np__1)) = np__1 ),
% 3.35/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7348,c_612]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7506,plain,
% 3.35/1.00      ( np__1 = k1_xboole_0
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_7501,c_20,c_7354]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7403,plain,
% 3.35/1.00      ( v1_relat_1(sK4(sK6)) ),
% 3.35/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7404,plain,
% 3.35/1.00      ( v1_relat_1(sK4(sK6)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_7403]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7677,plain,
% 3.35/1.00      ( np__1 = k1_xboole_0 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_7506,c_3407,c_7404]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7684,plain,
% 3.35/1.00      ( r2_hidden(k1_xboole_0,k2_relat_1(sK4(sK6))) = iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_7677,c_7052]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_15,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1,X2),X0) = X2 ),
% 3.35/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_617,plain,
% 3.35/1.00      ( k1_funct_1(sK3(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3102,plain,
% 3.35/1.00      ( k1_funct_1(sK3(k1_relat_1(X0),X1),sK2(X0,X2)) = X1
% 3.35/1.00      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_618,c_617]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9657,plain,
% 3.35/1.00      ( k1_funct_1(sK3(k1_relat_1(sK4(sK6)),X0),sK2(sK4(sK6),k1_xboole_0)) = X0
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_7684,c_3102]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_16,plain,
% 3.35/1.00      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1188,plain,
% 3.35/1.00      ( sK3(X0,X1) = X2
% 3.35/1.00      | k1_relat_1(X2) != sK6
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | v1_funct_1(X2) != iProver_top
% 3.35/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.35/1.00      | v1_relat_1(X2) != iProver_top
% 3.35/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_16,c_608]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_18,plain,
% 3.35/1.00      ( v1_relat_1(sK3(X0,X1)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_52,plain,
% 3.35/1.00      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_17,plain,
% 3.35/1.00      ( v1_funct_1(sK3(X0,X1)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_55,plain,
% 3.35/1.00      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1501,plain,
% 3.35/1.00      ( v1_relat_1(X2) != iProver_top
% 3.35/1.00      | sK3(X0,X1) = X2
% 3.35/1.00      | k1_relat_1(X2) != sK6
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_1188,c_52,c_55]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1502,plain,
% 3.35/1.00      ( sK3(X0,X1) = X2
% 3.35/1.00      | k1_relat_1(X2) != sK6
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | v1_funct_1(X2) != iProver_top
% 3.35/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.35/1.00      inference(renaming,[status(thm)],[c_1501]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1512,plain,
% 3.35/1.00      ( sK3(X0,X1) = sK4(X2)
% 3.35/1.00      | sK6 != X2
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | v1_funct_1(sK4(X2)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(X2)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_20,c_1502]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1278,plain,
% 3.35/1.00      ( sK3(X0,X1) = sK4(X2)
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | sK6 != X2
% 3.35/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_16,c_1269]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1311,plain,
% 3.35/1.00      ( ~ v1_funct_1(sK3(X0,X1))
% 3.35/1.00      | ~ v1_relat_1(sK3(X0,X1))
% 3.35/1.00      | sK3(X0,X1) = sK4(X2)
% 3.35/1.00      | sK6 != X0
% 3.35/1.00      | sK6 != X2 ),
% 3.35/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1278]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1656,plain,
% 3.35/1.00      ( sK3(X0,X1) = sK4(X2) | sK6 != X2 | sK6 != X0 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_1512,c_18,c_17,c_1311]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1657,plain,
% 3.35/1.00      ( sK3(X0,X1) = sK4(X2) | sK6 != X0 | sK6 != X2 ),
% 3.35/1.00      inference(renaming,[status(thm)],[c_1656]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1661,plain,
% 3.35/1.00      ( sK3(sK6,X0) = sK4(X1) | sK6 != X1 ),
% 3.35/1.00      inference(equality_resolution,[status(thm)],[c_1657]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2226,plain,
% 3.35/1.00      ( sK3(sK6,X0) = sK4(sK6) ),
% 3.35/1.00      inference(equality_resolution,[status(thm)],[c_1661]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7680,plain,
% 3.35/1.00      ( k1_funct_1(sK4(sK6),sK2(sK4(sK6),k1_xboole_0)) = k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_7677,c_7354]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9685,plain,
% 3.35/1.00      ( k1_xboole_0 = X0
% 3.35/1.00      | v1_funct_1(sK4(sK6)) != iProver_top
% 3.35/1.00      | v1_relat_1(sK4(sK6)) != iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_9657,c_20,c_2226,c_7680]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9878,plain,
% 3.35/1.00      ( k1_xboole_0 = X0 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_9685,c_3407,c_7404]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_820,plain,
% 3.35/1.00      ( k1_relat_1(X0) != sK6
% 3.35/1.00      | sK6 != k1_xboole_0
% 3.35/1.00      | k1_xboole_0 = X0
% 3.35/1.00      | v1_funct_1(X0) != iProver_top
% 3.35/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.35/1.00      | v1_relat_1(X0) != iProver_top
% 3.35/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_8,c_608]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_855,plain,
% 3.35/1.00      ( sK6 != k1_xboole_0 ),
% 3.35/1.00      inference(global_propositional_subsumption,
% 3.35/1.00                [status(thm)],
% 3.35/1.00                [c_820,c_27,c_86,c_87,c_853]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9964,plain,
% 3.35/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_9878,c_855]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_9966,plain,
% 3.35/1.00      ( $false ),
% 3.35/1.00      inference(equality_resolution_simp,[status(thm)],[c_9964]) ).
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  ------                               Statistics
% 3.35/1.00  
% 3.35/1.00  ------ General
% 3.35/1.00  
% 3.35/1.00  abstr_ref_over_cycles:                  0
% 3.35/1.00  abstr_ref_under_cycles:                 0
% 3.35/1.00  gc_basic_clause_elim:                   0
% 3.35/1.00  forced_gc_time:                         0
% 3.35/1.00  parsing_time:                           0.007
% 3.35/1.00  unif_index_cands_time:                  0.
% 3.35/1.00  unif_index_add_time:                    0.
% 3.35/1.00  orderings_time:                         0.
% 3.35/1.00  out_proof_time:                         0.01
% 3.35/1.00  total_time:                             0.3
% 3.35/1.00  num_of_symbols:                         48
% 3.35/1.00  num_of_terms:                           10741
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing
% 3.35/1.00  
% 3.35/1.00  num_of_splits:                          0
% 3.35/1.00  num_of_split_atoms:                     0
% 3.35/1.00  num_of_reused_defs:                     0
% 3.35/1.00  num_eq_ax_congr_red:                    20
% 3.35/1.00  num_of_sem_filtered_clauses:            1
% 3.35/1.00  num_of_subtypes:                        0
% 3.35/1.00  monotx_restored_types:                  0
% 3.35/1.00  sat_num_of_epr_types:                   0
% 3.35/1.00  sat_num_of_non_cyclic_types:            0
% 3.35/1.00  sat_guarded_non_collapsed_types:        0
% 3.35/1.00  num_pure_diseq_elim:                    0
% 3.35/1.00  simp_replaced_by:                       0
% 3.35/1.00  res_preprocessed:                       108
% 3.35/1.00  prep_upred:                             0
% 3.35/1.00  prep_unflattend:                        0
% 3.35/1.00  smt_new_axioms:                         0
% 3.35/1.00  pred_elim_cands:                        4
% 3.35/1.00  pred_elim:                              0
% 3.35/1.00  pred_elim_cl:                           0
% 3.35/1.00  pred_elim_cycles:                       1
% 3.35/1.00  merged_defs:                            0
% 3.35/1.00  merged_defs_ncl:                        0
% 3.35/1.00  bin_hyper_res:                          0
% 3.35/1.00  prep_cycles:                            3
% 3.35/1.00  pred_elim_time:                         0.
% 3.35/1.00  splitting_time:                         0.
% 3.35/1.00  sem_filter_time:                        0.
% 3.35/1.00  monotx_time:                            0.
% 3.35/1.00  subtype_inf_time:                       0.
% 3.35/1.00  
% 3.35/1.00  ------ Problem properties
% 3.35/1.00  
% 3.35/1.00  clauses:                                29
% 3.35/1.00  conjectures:                            2
% 3.35/1.00  epr:                                    3
% 3.35/1.00  horn:                                   26
% 3.35/1.00  ground:                                 4
% 3.35/1.00  unary:                                  16
% 3.35/1.00  binary:                                 4
% 3.35/1.00  lits:                                   65
% 3.35/1.00  lits_eq:                                24
% 3.35/1.00  fd_pure:                                0
% 3.35/1.00  fd_pseudo:                              0
% 3.35/1.00  fd_cond:                                2
% 3.35/1.00  fd_pseudo_cond:                         4
% 3.35/1.00  ac_symbols:                             0
% 3.35/1.00  
% 3.35/1.00  ------ Propositional Solver
% 3.35/1.00  
% 3.35/1.00  prop_solver_calls:                      24
% 3.35/1.00  prop_fast_solver_calls:                 938
% 3.35/1.00  smt_solver_calls:                       0
% 3.35/1.00  smt_fast_solver_calls:                  0
% 3.35/1.00  prop_num_of_clauses:                    4147
% 3.35/1.00  prop_preprocess_simplified:             8455
% 3.35/1.00  prop_fo_subsumed:                       59
% 3.35/1.00  prop_solver_time:                       0.
% 3.35/1.00  smt_solver_time:                        0.
% 3.35/1.00  smt_fast_solver_time:                   0.
% 3.35/1.00  prop_fast_solver_time:                  0.
% 3.35/1.00  prop_unsat_core_time:                   0.
% 3.35/1.00  
% 3.35/1.00  ------ QBF
% 3.35/1.00  
% 3.35/1.00  qbf_q_res:                              0
% 3.35/1.00  qbf_num_tautologies:                    0
% 3.35/1.00  qbf_prep_cycles:                        0
% 3.35/1.00  
% 3.35/1.00  ------ BMC1
% 3.35/1.00  
% 3.35/1.00  bmc1_current_bound:                     -1
% 3.35/1.00  bmc1_last_solved_bound:                 -1
% 3.35/1.00  bmc1_unsat_core_size:                   -1
% 3.35/1.00  bmc1_unsat_core_parents_size:           -1
% 3.35/1.00  bmc1_merge_next_fun:                    0
% 3.35/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.35/1.00  
% 3.35/1.00  ------ Instantiation
% 3.35/1.00  
% 3.35/1.00  inst_num_of_clauses:                    1082
% 3.35/1.00  inst_num_in_passive:                    265
% 3.35/1.00  inst_num_in_active:                     513
% 3.35/1.00  inst_num_in_unprocessed:                331
% 3.35/1.00  inst_num_of_loops:                      580
% 3.35/1.00  inst_num_of_learning_restarts:          0
% 3.35/1.00  inst_num_moves_active_passive:          65
% 3.35/1.00  inst_lit_activity:                      0
% 3.35/1.00  inst_lit_activity_moves:                0
% 3.35/1.00  inst_num_tautologies:                   0
% 3.35/1.00  inst_num_prop_implied:                  0
% 3.35/1.00  inst_num_existing_simplified:           0
% 3.35/1.00  inst_num_eq_res_simplified:             0
% 3.35/1.00  inst_num_child_elim:                    0
% 3.35/1.00  inst_num_of_dismatching_blockings:      333
% 3.35/1.00  inst_num_of_non_proper_insts:           1090
% 3.35/1.00  inst_num_of_duplicates:                 0
% 3.35/1.00  inst_inst_num_from_inst_to_res:         0
% 3.35/1.00  inst_dismatching_checking_time:         0.
% 3.35/1.00  
% 3.35/1.00  ------ Resolution
% 3.35/1.00  
% 3.35/1.00  res_num_of_clauses:                     0
% 3.35/1.00  res_num_in_passive:                     0
% 3.35/1.00  res_num_in_active:                      0
% 3.35/1.00  res_num_of_loops:                       111
% 3.35/1.00  res_forward_subset_subsumed:            34
% 3.35/1.00  res_backward_subset_subsumed:           54
% 3.35/1.00  res_forward_subsumed:                   0
% 3.35/1.00  res_backward_subsumed:                  0
% 3.35/1.00  res_forward_subsumption_resolution:     0
% 3.35/1.00  res_backward_subsumption_resolution:    0
% 3.35/1.00  res_clause_to_clause_subsumption:       740
% 3.35/1.00  res_orphan_elimination:                 0
% 3.35/1.00  res_tautology_del:                      44
% 3.35/1.00  res_num_eq_res_simplified:              0
% 3.35/1.00  res_num_sel_changes:                    0
% 3.35/1.00  res_moves_from_active_to_pass:          0
% 3.35/1.00  
% 3.35/1.00  ------ Superposition
% 3.35/1.00  
% 3.35/1.00  sup_time_total:                         0.
% 3.35/1.00  sup_time_generating:                    0.
% 3.35/1.00  sup_time_sim_full:                      0.
% 3.35/1.00  sup_time_sim_immed:                     0.
% 3.35/1.00  
% 3.35/1.00  sup_num_of_clauses:                     222
% 3.35/1.00  sup_num_in_active:                      12
% 3.35/1.00  sup_num_in_passive:                     210
% 3.35/1.00  sup_num_of_loops:                       115
% 3.35/1.00  sup_fw_superposition:                   225
% 3.35/1.00  sup_bw_superposition:                   152
% 3.35/1.00  sup_immediate_simplified:               103
% 3.35/1.00  sup_given_eliminated:                   0
% 3.35/1.00  comparisons_done:                       0
% 3.35/1.00  comparisons_avoided:                    3
% 3.35/1.00  
% 3.35/1.00  ------ Simplifications
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  sim_fw_subset_subsumed:                 15
% 3.35/1.00  sim_bw_subset_subsumed:                 13
% 3.35/1.00  sim_fw_subsumed:                        19
% 3.35/1.00  sim_bw_subsumed:                        2
% 3.35/1.00  sim_fw_subsumption_res:                 19
% 3.35/1.00  sim_bw_subsumption_res:                 0
% 3.35/1.00  sim_tautology_del:                      4
% 3.35/1.00  sim_eq_tautology_del:                   25
% 3.35/1.00  sim_eq_res_simp:                        0
% 3.35/1.00  sim_fw_demodulated:                     31
% 3.35/1.00  sim_bw_demodulated:                     99
% 3.35/1.00  sim_light_normalised:                   57
% 3.35/1.00  sim_joinable_taut:                      0
% 3.35/1.00  sim_joinable_simp:                      0
% 3.35/1.00  sim_ac_normalised:                      0
% 3.35/1.00  sim_smt_subsumption:                    0
% 3.35/1.00  
%------------------------------------------------------------------------------
