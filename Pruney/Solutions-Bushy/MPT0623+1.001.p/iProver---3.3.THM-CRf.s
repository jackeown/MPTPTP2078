%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:45 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 460 expanded)
%              Number of clauses        :   90 ( 160 expanded)
%              Number of leaves         :   23 ( 111 expanded)
%              Depth                    :   23
%              Number of atoms          :  485 (2098 expanded)
%              Number of equality atoms :  218 ( 857 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK4(X0,X1)) = X1
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK4(X0,X1)) = X1
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f38])).

fof(f59,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f39])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK5)
          | k1_relat_1(X2) != sK6
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 != sK5 ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f40])).

fof(f65,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f67,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,plain,
    ( m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_617,plain,
    ( m1_subset_1(o_1_0_funct_1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_610,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2761,plain,
    ( r2_hidden(o_1_0_funct_1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_610])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_625,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_619,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2643,plain,
    ( k1_funct_1(X0,sK3(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_619])).

cnf(c_16,plain,
    ( k1_relat_1(sK4(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_607,plain,
    ( k1_relat_1(X0) != sK6
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_879,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK4(X1,X0)),sK5) != iProver_top
    | v1_relat_1(sK4(X1,X0)) != iProver_top
    | v1_funct_1(sK4(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_607])).

cnf(c_888,plain,
    ( r1_tarski(k2_relat_1(sK4(X0,sK6)),sK5) != iProver_top
    | v1_relat_1(sK4(X0,sK6)) != iProver_top
    | v1_funct_1(sK4(X0,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_879])).

cnf(c_9183,plain,
    ( k1_funct_1(sK4(X0,sK6),sK3(sK4(X0,sK6),sK0(k2_relat_1(sK4(X0,sK6)),sK5))) = sK0(k2_relat_1(sK4(X0,sK6)),sK5)
    | v1_relat_1(sK4(X0,sK6)) != iProver_top
    | v1_funct_1(sK4(X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_888])).

cnf(c_889,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(X0,sK6)),sK5)
    | ~ v1_relat_1(sK4(X0,sK6))
    | ~ v1_funct_1(sK4(X0,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_888])).

cnf(c_17,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1004,plain,
    ( v1_funct_1(sK4(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1097,plain,
    ( v1_relat_1(sK4(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_843,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0))
    | r1_tarski(k2_relat_1(X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1131,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6)))
    | r1_tarski(k2_relat_1(sK4(X0,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1355,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6)))
    | ~ v1_relat_1(sK4(X0,sK6))
    | ~ v1_funct_1(sK4(X0,sK6))
    | k1_funct_1(sK4(X0,sK6),sK3(sK4(X0,sK6),sK0(k2_relat_1(sK4(X0,sK6)),sK5))) = sK0(k2_relat_1(sK4(X0,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10055,plain,
    ( k1_funct_1(sK4(X0,sK6),sK3(sK4(X0,sK6),sK0(k2_relat_1(sK4(X0,sK6)),sK5))) = sK0(k2_relat_1(sK4(X0,sK6)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9183,c_889,c_1004,c_1097,c_1131,c_1355])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_620,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10060,plain,
    ( r2_hidden(sK3(sK4(X0,sK6),sK0(k2_relat_1(sK4(X0,sK6)),sK5)),k1_relat_1(sK4(X0,sK6))) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6))) = iProver_top
    | v1_relat_1(sK4(X0,sK6)) != iProver_top
    | v1_funct_1(sK4(X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10055,c_620])).

cnf(c_10065,plain,
    ( r2_hidden(sK3(sK4(X0,sK6),sK0(k2_relat_1(sK4(X0,sK6)),sK5)),sK6) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6))) = iProver_top
    | v1_relat_1(sK4(X0,sK6)) != iProver_top
    | v1_funct_1(sK4(X0,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10060,c_16])).

cnf(c_1005,plain,
    ( v1_funct_1(sK4(X0,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1098,plain,
    ( v1_relat_1(sK4(X0,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1132,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6))) = iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,sK6)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_10090,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK6)),sK5),k2_relat_1(sK4(X0,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10065,c_888,c_1005,c_1098,c_1132])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_618,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X2,X1),X0) = o_1_0_funct_1(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_613,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = o_1_0_funct_1(X0)
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2092,plain,
    ( k1_funct_1(sK4(X0,k1_relat_1(X1)),sK3(X1,X2)) = o_1_0_funct_1(X0)
    | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_613])).

cnf(c_10100,plain,
    ( k1_funct_1(sK4(X0,k1_relat_1(sK4(X1,sK6))),sK3(sK4(X1,sK6),sK0(k2_relat_1(sK4(X1,sK6)),sK5))) = o_1_0_funct_1(X0)
    | v1_relat_1(sK4(X1,sK6)) != iProver_top
    | v1_funct_1(sK4(X1,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10090,c_2092])).

cnf(c_10104,plain,
    ( k1_funct_1(sK4(X0,sK6),sK3(sK4(X1,sK6),sK0(k2_relat_1(sK4(X1,sK6)),sK5))) = o_1_0_funct_1(X0)
    | v1_relat_1(sK4(X1,sK6)) != iProver_top
    | v1_funct_1(sK4(X1,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10100,c_16])).

cnf(c_612,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_611,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10589,plain,
    ( k1_funct_1(sK4(X0,sK6),sK3(sK4(X1,sK6),sK0(k2_relat_1(sK4(X1,sK6)),sK5))) = o_1_0_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10104,c_612,c_611])).

cnf(c_10591,plain,
    ( sK0(k2_relat_1(sK4(X0,sK6)),sK5) = o_1_0_funct_1(X0) ),
    inference(demodulation,[status(thm)],[c_10589,c_10055])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_626,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10695,plain,
    ( r2_hidden(o_1_0_funct_1(X0),sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,sK6)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10591,c_626])).

cnf(c_11913,plain,
    ( r2_hidden(o_1_0_funct_1(X0),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10695,c_888,c_1005,c_1098])).

cnf(c_11920,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_11913])).

cnf(c_217,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1570,plain,
    ( ~ v1_relat_1(sK6)
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK5 ),
    inference(resolution,[status(thm)],[c_217,c_23])).

cnf(c_25,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK5)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_46,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_78,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_81,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_funct_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_873,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),sK5)
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_875,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK5)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_214,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_929,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(X0) = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_930,plain,
    ( k1_relat_1(k1_xboole_0) = sK6
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_923,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1038,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_1040,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_213,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1039,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_1010,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1142,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_1144,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_1143,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_615,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_608,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1372,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_608])).

cnf(c_1390,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_616,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1690,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_608])).

cnf(c_1720,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_1745,plain,
    ( k1_xboole_0 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1570,c_23,c_25,c_31,c_14,c_46,c_78,c_81,c_875,c_930,c_1040,c_1039,c_1144,c_1143,c_1390,c_1720])).

cnf(c_840,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_841,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11920,c_1745,c_841])).


%------------------------------------------------------------------------------
