%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0623+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:45 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 514 expanded)
%              Number of clauses        :   78 ( 155 expanded)
%              Number of leaves         :   19 ( 129 expanded)
%              Depth                    :   21
%              Number of atoms          :  442 (2437 expanded)
%              Number of equality atoms :  192 ( 910 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f15])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f32,f31,f30])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = o_1_0_funct_1(X0)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK5(X0,X1)) = X1
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK5(X0,X1)) = X1
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f36])).

fof(f55,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK6)
          | k1_relat_1(X2) != sK7
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 != sK6 ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f39])).

fof(f64,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f66,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK5(X0,X1),X3) = o_1_0_funct_1(X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_795,plain,
    ( m1_subset_1(o_1_0_funct_1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_789,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1958,plain,
    ( r2_hidden(o_1_0_funct_1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_789])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_803,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_797,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2051,plain,
    ( k1_funct_1(X0,sK3(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_797])).

cnf(c_13,plain,
    ( k1_relat_1(sK5(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_784,plain,
    ( k1_relat_1(X0) != sK7
    | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1074,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK5(X1,X0)),sK6) != iProver_top
    | v1_relat_1(sK5(X1,X0)) != iProver_top
    | v1_funct_1(sK5(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_784])).

cnf(c_1083,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) != iProver_top
    | v1_relat_1(sK5(X0,sK7)) != iProver_top
    | v1_funct_1(sK5(X0,sK7)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1074])).

cnf(c_11013,plain,
    ( k1_funct_1(sK5(X0,sK7),sK3(sK5(X0,sK7),sK0(k2_relat_1(sK5(X0,sK7)),sK6))) = sK0(k2_relat_1(sK5(X0,sK7)),sK6)
    | v1_relat_1(sK5(X0,sK7)) != iProver_top
    | v1_funct_1(sK5(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_1083])).

cnf(c_1449,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6)
    | ~ v1_relat_1(sK5(X0,sK7))
    | ~ v1_funct_1(sK5(X0,sK7)) ),
    inference(resolution,[status(thm)],[c_22,c_13])).

cnf(c_14,plain,
    ( v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1560,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1449,c_14,c_15])).

cnf(c_1608,plain,
    ( v1_funct_1(sK5(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1791,plain,
    ( v1_relat_1(sK5(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1034,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
    | r1_tarski(k2_relat_1(X0),sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3100,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7)))
    | r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_6986,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7)))
    | ~ v1_relat_1(sK5(X0,sK7))
    | ~ v1_funct_1(sK5(X0,sK7))
    | k1_funct_1(sK5(X0,sK7),sK3(sK5(X0,sK7),sK0(k2_relat_1(sK5(X0,sK7)),sK6))) = sK0(k2_relat_1(sK5(X0,sK7)),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11876,plain,
    ( k1_funct_1(sK5(X0,sK7),sK3(sK5(X0,sK7),sK0(k2_relat_1(sK5(X0,sK7)),sK6))) = sK0(k2_relat_1(sK5(X0,sK7)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11013,c_1560,c_1608,c_1791,c_3100,c_6986])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_798,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11881,plain,
    ( r2_hidden(sK3(sK5(X0,sK7),sK0(k2_relat_1(sK5(X0,sK7)),sK6)),k1_relat_1(sK5(X0,sK7))) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7))) = iProver_top
    | v1_relat_1(sK5(X0,sK7)) != iProver_top
    | v1_funct_1(sK5(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11876,c_798])).

cnf(c_11886,plain,
    ( r2_hidden(sK3(sK5(X0,sK7),sK0(k2_relat_1(sK5(X0,sK7)),sK6)),sK7) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7))) = iProver_top
    | v1_relat_1(sK5(X0,sK7)) != iProver_top
    | v1_funct_1(sK5(X0,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11881,c_13])).

cnf(c_1561,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_3101,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7))) = iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3100])).

cnf(c_11911,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(X0,sK7)),sK6),k2_relat_1(sK5(X0,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11886,c_1561,c_3101])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_796,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1808,plain,
    ( r2_hidden(X0,k2_relat_1(sK5(X1,X2))) != iProver_top
    | r2_hidden(sK3(sK5(X1,X2),X0),X2) = iProver_top
    | v1_relat_1(sK5(X1,X2)) != iProver_top
    | v1_funct_1(sK5(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_796])).

cnf(c_791,plain,
    ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_790,plain,
    ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3588,plain,
    ( r2_hidden(X0,k2_relat_1(sK5(X1,X2))) != iProver_top
    | r2_hidden(sK3(sK5(X1,X2),X0),X2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1808,c_791,c_790])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X2,X1),X0) = o_1_0_funct_1(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_792,plain,
    ( k1_funct_1(sK5(X0,X1),X2) = o_1_0_funct_1(X0)
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3592,plain,
    ( k1_funct_1(sK5(X0,X1),sK3(sK5(X2,X1),X3)) = o_1_0_funct_1(X0)
    | r2_hidden(X3,k2_relat_1(sK5(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3588,c_792])).

cnf(c_11925,plain,
    ( k1_funct_1(sK5(X0,sK7),sK3(sK5(X1,sK7),sK0(k2_relat_1(sK5(X1,sK7)),sK6))) = o_1_0_funct_1(X0) ),
    inference(superposition,[status(thm)],[c_11911,c_3592])).

cnf(c_12257,plain,
    ( sK0(k2_relat_1(sK5(X0,sK7)),sK6) = o_1_0_funct_1(X0) ),
    inference(demodulation,[status(thm)],[c_11925,c_11876])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_804,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12306,plain,
    ( r2_hidden(o_1_0_funct_1(X0),sK6) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,sK7)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12257,c_804])).

cnf(c_12528,plain,
    ( r2_hidden(o_1_0_funct_1(X0),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12306,c_1561])).

cnf(c_12535,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_12528])).

cnf(c_1936,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_804])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_157])).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_158])).

cnf(c_783,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_3594,plain,
    ( r2_hidden(X0,k2_relat_1(sK5(X1,X2))) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_xboole_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3588,c_783])).

cnf(c_4265,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X2,X0)),X3) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_3594])).

cnf(c_4354,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,X1)),X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_4265])).

cnf(c_4714,plain,
    ( v1_xboole_0(sK7) != iProver_top
    | v1_relat_1(sK5(X0,sK7)) != iProver_top
    | v1_funct_1(sK5(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4354,c_1083])).

cnf(c_265,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_264,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2087,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_265,c_264])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2251,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(resolution,[status(thm)],[c_2087,c_23])).

cnf(c_273,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2263,plain,
    ( v1_xboole_0(sK7)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK6 ),
    inference(resolution,[status(thm)],[c_2251,c_273])).

cnf(c_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2442,plain,
    ( v1_xboole_0(sK7)
    | k1_xboole_0 != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2263,c_11])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2458,plain,
    ( v1_xboole_0(sK7)
    | ~ v1_xboole_0(sK6) ),
    inference(resolution,[status(thm)],[c_2442,c_21])).

cnf(c_2459,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2458])).

cnf(c_1792,plain,
    ( v1_relat_1(sK5(X0,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_1609,plain,
    ( v1_funct_1(sK5(X0,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1608])).

cnf(c_12540,plain,
    ( v1_xboole_0(sK7) != iProver_top
    | v1_relat_1(sK5(k1_xboole_0,sK7)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0,sK7)) != iProver_top ),
    inference(grounding,[status(thm)],[c_4714:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_12541,plain,
    ( v1_relat_1(sK5(k1_xboole_0,sK7)) = iProver_top ),
    inference(grounding,[status(thm)],[c_1792:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_12542,plain,
    ( v1_funct_1(sK5(k1_xboole_0,sK7)) = iProver_top ),
    inference(grounding,[status(thm)],[c_1609:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12535,c_12540,c_2459,c_12541,c_12542])).


%------------------------------------------------------------------------------
