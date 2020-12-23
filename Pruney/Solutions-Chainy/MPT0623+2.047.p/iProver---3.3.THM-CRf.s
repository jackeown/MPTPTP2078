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
% DateTime   : Thu Dec  3 11:49:39 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 372 expanded)
%              Number of clauses        :   69 ( 139 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  405 (1498 expanded)
%              Number of equality atoms :  235 ( 798 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
          & k1_relat_1(sK4(X0,X1)) = X0
          & v1_funct_1(sK4(X0,X1))
          & v1_relat_1(sK4(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK4(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,
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

fof(f38,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f37])).

fof(f64,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

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
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f33])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f66,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_839,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_842,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_834,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1574,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_834])).

cnf(c_20,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_825,plain,
    ( k1_relat_1(X0) != sK6
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1103,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_825])).

cnf(c_23,plain,
    ( v1_relat_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( v1_funct_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1297,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_29,c_32])).

cnf(c_1304,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1297])).

cnf(c_1319,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1304])).

cnf(c_2200,plain,
    ( sK0(k1_tarski(X0),sK5) = X0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1574,c_1319])).

cnf(c_17,plain,
    ( k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_43,plain,
    ( k1_relat_1(sK3(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_290,plain,
    ( sK3(X0) != X1
    | k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_291,plain,
    ( k2_relat_1(sK3(X0)) = k1_xboole_0
    | k1_relat_1(sK3(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_292,plain,
    ( k2_relat_1(sK3(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(sK3(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1056,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top
    | v1_funct_1(sK3(X0)) != iProver_top
    | v1_relat_1(sK3(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_825])).

cnf(c_37,plain,
    ( v1_relat_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_40,plain,
    ( v1_funct_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1061,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1056,c_37,c_40])).

cnf(c_1063,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),sK5)
    | sK6 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1061])).

cnf(c_1065,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK5)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_477,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1093,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3(X2)),sK5)
    | k2_relat_1(sK3(X2)) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1432,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(k2_relat_1(sK3(X1)),sK5)
    | k2_relat_1(sK3(X1)) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1435,plain,
    ( r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | k2_relat_1(sK3(k1_xboole_0)) != k1_xboole_0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_475,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1433,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1722,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2585,plain,
    ( sK0(k1_tarski(X0),sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_43,c_292,c_1065,c_1435,c_1433,c_1722])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_843,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2589,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_843])).

cnf(c_2933,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2589,c_43,c_292,c_1065,c_1319,c_1435,c_1433,c_1722])).

cnf(c_2942,plain,
    ( sK5 = X0
    | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_2933])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_833,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1403,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_833])).

cnf(c_3160,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2942,c_1403])).

cnf(c_476,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1843,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_3144,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_3146,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3022,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1828,plain,
    ( ~ r2_hidden(sK6,k1_tarski(X0))
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3021,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_1050,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_1051,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_57,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3160,c_3146,c_3022,c_3021,c_1722,c_1433,c_1435,c_1065,c_1051,c_292,c_57,c_56,c_43,c_25])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.00  
% 2.73/1.00  ------  iProver source info
% 2.73/1.00  
% 2.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.00  git: non_committed_changes: false
% 2.73/1.00  git: last_make_outside_of_git: false
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     num_symb
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       true
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  ------ Parsing...
% 2.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.00  ------ Proving...
% 2.73/1.00  ------ Problem Properties 
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  clauses                                 26
% 2.73/1.00  conjectures                             2
% 2.73/1.00  EPR                                     3
% 2.73/1.00  Horn                                    18
% 2.73/1.00  unary                                   8
% 2.73/1.00  binary                                  9
% 2.73/1.00  lits                                    54
% 2.73/1.00  lits eq                                 27
% 2.73/1.00  fd_pure                                 0
% 2.73/1.00  fd_pseudo                               0
% 2.73/1.00  fd_cond                                 4
% 2.73/1.00  fd_pseudo_cond                          4
% 2.73/1.00  AC symbols                              0
% 2.73/1.00  
% 2.73/1.00  ------ Schedule dynamic 5 is on 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  Current options:
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     none
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       false
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ Proving...
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS status Theorem for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  fof(f2,axiom,(
% 2.73/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f13,plain,(
% 2.73/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f2])).
% 2.73/1.00  
% 2.73/1.00  fof(f23,plain,(
% 2.73/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.73/1.00    inference(nnf_transformation,[],[f13])).
% 2.73/1.00  
% 2.73/1.00  fof(f24,plain,(
% 2.73/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f25,plain,(
% 2.73/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 2.73/1.00  
% 2.73/1.00  fof(f42,plain,(
% 2.73/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f1,axiom,(
% 2.73/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f12,plain,(
% 2.73/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f1])).
% 2.73/1.00  
% 2.73/1.00  fof(f19,plain,(
% 2.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/1.00    inference(nnf_transformation,[],[f12])).
% 2.73/1.00  
% 2.73/1.00  fof(f20,plain,(
% 2.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/1.00    inference(rectify,[],[f19])).
% 2.73/1.00  
% 2.73/1.00  fof(f21,plain,(
% 2.73/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f22,plain,(
% 2.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 2.73/1.00  
% 2.73/1.00  fof(f40,plain,(
% 2.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f22])).
% 2.73/1.00  
% 2.73/1.00  fof(f4,axiom,(
% 2.73/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f26,plain,(
% 2.73/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.73/1.00    inference(nnf_transformation,[],[f4])).
% 2.73/1.00  
% 2.73/1.00  fof(f27,plain,(
% 2.73/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.73/1.00    inference(rectify,[],[f26])).
% 2.73/1.00  
% 2.73/1.00  fof(f28,plain,(
% 2.73/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f29,plain,(
% 2.73/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 2.73/1.00  
% 2.73/1.00  fof(f45,plain,(
% 2.73/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.73/1.00    inference(cnf_transformation,[],[f29])).
% 2.73/1.00  
% 2.73/1.00  fof(f67,plain,(
% 2.73/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.73/1.00    inference(equality_resolution,[],[f45])).
% 2.73/1.00  
% 2.73/1.00  fof(f9,axiom,(
% 2.73/1.00    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f16,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 2.73/1.00    inference(ennf_transformation,[],[f9])).
% 2.73/1.00  
% 2.73/1.00  fof(f35,plain,(
% 2.73/1.00    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f36,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))) | k1_xboole_0 = X0)),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f35])).
% 2.73/1.00  
% 2.73/1.00  fof(f62,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f36])).
% 2.73/1.00  
% 2.73/1.00  fof(f61,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f36])).
% 2.73/1.00  
% 2.73/1.00  fof(f10,conjecture,(
% 2.73/1.00    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f11,negated_conjecture,(
% 2.73/1.00    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.73/1.00    inference(negated_conjecture,[],[f10])).
% 2.73/1.00  
% 2.73/1.00  fof(f17,plain,(
% 2.73/1.00    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.73/1.00    inference(ennf_transformation,[],[f11])).
% 2.73/1.00  
% 2.73/1.00  fof(f18,plain,(
% 2.73/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.73/1.00    inference(flattening,[],[f17])).
% 2.73/1.00  
% 2.73/1.00  fof(f37,plain,(
% 2.73/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f38,plain,(
% 2.73/1.00    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f37])).
% 2.73/1.00  
% 2.73/1.00  fof(f64,plain,(
% 2.73/1.00    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f38])).
% 2.73/1.00  
% 2.73/1.00  fof(f59,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f36])).
% 2.73/1.00  
% 2.73/1.00  fof(f60,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f36])).
% 2.73/1.00  
% 2.73/1.00  fof(f8,axiom,(
% 2.73/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f15,plain,(
% 2.73/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.73/1.00    inference(ennf_transformation,[],[f8])).
% 2.73/1.00  
% 2.73/1.00  fof(f33,plain,(
% 2.73/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f34,plain,(
% 2.73/1.00    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f33])).
% 2.73/1.00  
% 2.73/1.00  fof(f57,plain,(
% 2.73/1.00    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f34])).
% 2.73/1.00  
% 2.73/1.00  fof(f7,axiom,(
% 2.73/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f14,plain,(
% 2.73/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.73/1.00    inference(ennf_transformation,[],[f7])).
% 2.73/1.00  
% 2.73/1.00  fof(f32,plain,(
% 2.73/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.73/1.00    inference(nnf_transformation,[],[f14])).
% 2.73/1.00  
% 2.73/1.00  fof(f53,plain,(
% 2.73/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f32])).
% 2.73/1.00  
% 2.73/1.00  fof(f55,plain,(
% 2.73/1.00    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f34])).
% 2.73/1.00  
% 2.73/1.00  fof(f56,plain,(
% 2.73/1.00    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f34])).
% 2.73/1.00  
% 2.73/1.00  fof(f3,axiom,(
% 2.73/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f44,plain,(
% 2.73/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f3])).
% 2.73/1.00  
% 2.73/1.00  fof(f41,plain,(
% 2.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f22])).
% 2.73/1.00  
% 2.73/1.00  fof(f5,axiom,(
% 2.73/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f30,plain,(
% 2.73/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/1.00    inference(nnf_transformation,[],[f5])).
% 2.73/1.00  
% 2.73/1.00  fof(f31,plain,(
% 2.73/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/1.00    inference(flattening,[],[f30])).
% 2.73/1.00  
% 2.73/1.00  fof(f51,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f68,plain,(
% 2.73/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.73/1.00    inference(equality_resolution,[],[f51])).
% 2.73/1.00  
% 2.73/1.00  fof(f6,axiom,(
% 2.73/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f52,plain,(
% 2.73/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f6])).
% 2.73/1.00  
% 2.73/1.00  fof(f46,plain,(
% 2.73/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.73/1.00    inference(cnf_transformation,[],[f29])).
% 2.73/1.00  
% 2.73/1.00  fof(f65,plain,(
% 2.73/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.73/1.00    inference(equality_resolution,[],[f46])).
% 2.73/1.00  
% 2.73/1.00  fof(f66,plain,(
% 2.73/1.00    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.73/1.00    inference(equality_resolution,[],[f65])).
% 2.73/1.00  
% 2.73/1.00  fof(f50,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f69,plain,(
% 2.73/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.73/1.00    inference(equality_resolution,[],[f50])).
% 2.73/1.00  
% 2.73/1.00  fof(f49,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f63,plain,(
% 2.73/1.00    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 2.73/1.00    inference(cnf_transformation,[],[f38])).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4,plain,
% 2.73/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_839,plain,
% 2.73/1.00      ( X0 = X1
% 2.73/1.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 2.73/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1,plain,
% 2.73/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_842,plain,
% 2.73/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.73/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9,plain,
% 2.73/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.73/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_834,plain,
% 2.73/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1574,plain,
% 2.73/1.00      ( sK0(k1_tarski(X0),X1) = X0
% 2.73/1.00      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_842,c_834]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,plain,
% 2.73/1.00      ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_21,plain,
% 2.73/1.00      ( k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_24,negated_conjecture,
% 2.73/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k1_relat_1(X0) != sK6 ),
% 2.73/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_825,plain,
% 2.73/1.00      ( k1_relat_1(X0) != sK6
% 2.73/1.00      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 2.73/1.00      | v1_funct_1(X0) != iProver_top
% 2.73/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1103,plain,
% 2.73/1.00      ( sK6 != X0
% 2.73/1.00      | k1_xboole_0 = X0
% 2.73/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
% 2.73/1.00      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 2.73/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_21,c_825]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_23,plain,
% 2.73/1.00      ( v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_29,plain,
% 2.73/1.00      ( k1_xboole_0 = X0 | v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,plain,
% 2.73/1.00      ( v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_32,plain,
% 2.73/1.00      ( k1_xboole_0 = X0 | v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1297,plain,
% 2.73/1.00      ( sK6 != X0
% 2.73/1.00      | k1_xboole_0 = X0
% 2.73/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1103,c_29,c_32]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1304,plain,
% 2.73/1.00      ( sK6 = k1_xboole_0
% 2.73/1.00      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
% 2.73/1.00      inference(equality_resolution,[status(thm)],[c_1297]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1319,plain,
% 2.73/1.00      ( sK6 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_20,c_1304]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2200,plain,
% 2.73/1.00      ( sK0(k1_tarski(X0),sK5) = X0 | sK6 = k1_xboole_0 ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1574,c_1319]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_17,plain,
% 2.73/1.00      ( k1_relat_1(sK3(X0)) = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_43,plain,
% 2.73/1.00      ( k1_relat_1(sK3(k1_xboole_0)) = k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_15,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0)
% 2.73/1.00      | k2_relat_1(X0) = k1_xboole_0
% 2.73/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_19,plain,
% 2.73/1.00      ( v1_relat_1(sK3(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_290,plain,
% 2.73/1.00      ( sK3(X0) != X1
% 2.73/1.00      | k2_relat_1(X1) = k1_xboole_0
% 2.73/1.00      | k1_relat_1(X1) != k1_xboole_0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_291,plain,
% 2.73/1.00      ( k2_relat_1(sK3(X0)) = k1_xboole_0
% 2.73/1.00      | k1_relat_1(sK3(X0)) != k1_xboole_0 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_292,plain,
% 2.73/1.00      ( k2_relat_1(sK3(k1_xboole_0)) = k1_xboole_0
% 2.73/1.00      | k1_relat_1(sK3(k1_xboole_0)) != k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_291]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1056,plain,
% 2.73/1.00      ( sK6 != X0
% 2.73/1.00      | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top
% 2.73/1.00      | v1_funct_1(sK3(X0)) != iProver_top
% 2.73/1.00      | v1_relat_1(sK3(X0)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_17,c_825]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_37,plain,
% 2.73/1.00      ( v1_relat_1(sK3(X0)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_18,plain,
% 2.73/1.00      ( v1_funct_1(sK3(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_40,plain,
% 2.73/1.00      ( v1_funct_1(sK3(X0)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1061,plain,
% 2.73/1.00      ( sK6 != X0 | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1056,c_37,c_40]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1063,plain,
% 2.73/1.00      ( ~ r1_tarski(k2_relat_1(sK3(X0)),sK5) | sK6 != X0 ),
% 2.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1061]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1065,plain,
% 2.73/1.00      ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK5)
% 2.73/1.00      | sK6 != k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_477,plain,
% 2.73/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.73/1.00      theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1093,plain,
% 2.73/1.00      ( ~ r1_tarski(X0,X1)
% 2.73/1.00      | r1_tarski(k2_relat_1(sK3(X2)),sK5)
% 2.73/1.00      | k2_relat_1(sK3(X2)) != X0
% 2.73/1.00      | sK5 != X1 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1432,plain,
% 2.73/1.00      ( ~ r1_tarski(X0,sK5)
% 2.73/1.00      | r1_tarski(k2_relat_1(sK3(X1)),sK5)
% 2.73/1.00      | k2_relat_1(sK3(X1)) != X0
% 2.73/1.00      | sK5 != sK5 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1093]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1435,plain,
% 2.73/1.00      ( r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK5)
% 2.73/1.00      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.73/1.00      | k2_relat_1(sK3(k1_xboole_0)) != k1_xboole_0
% 2.73/1.00      | sK5 != sK5 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1432]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_475,plain,( X0 = X0 ),theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1433,plain,
% 2.73/1.00      ( sK5 = sK5 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_475]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5,plain,
% 2.73/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1722,plain,
% 2.73/1.00      ( r1_tarski(k1_xboole_0,sK5) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2585,plain,
% 2.73/1.00      ( sK0(k1_tarski(X0),sK5) = X0 ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2200,c_43,c_292,c_1065,c_1435,c_1433,c_1722]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_0,plain,
% 2.73/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_843,plain,
% 2.73/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.73/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2589,plain,
% 2.73/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 2.73/1.00      | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_2585,c_843]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2933,plain,
% 2.73/1.00      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2589,c_43,c_292,c_1065,c_1319,c_1435,c_1433,c_1722]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2942,plain,
% 2.73/1.00      ( sK5 = X0 | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_839,c_2933]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_10,plain,
% 2.73/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_13,plain,
% 2.73/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_833,plain,
% 2.73/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1403,plain,
% 2.73/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_10,c_833]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3160,plain,
% 2.73/1.00      ( sK5 = k1_xboole_0 ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_2942,c_1403]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_476,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1843,plain,
% 2.73/1.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_476]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3144,plain,
% 2.73/1.00      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1843]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3146,plain,
% 2.73/1.00      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_3144]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_8,plain,
% 2.73/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3022,plain,
% 2.73/1.00      ( r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1828,plain,
% 2.73/1.00      ( ~ r2_hidden(sK6,k1_tarski(X0)) | sK6 = X0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3021,plain,
% 2.73/1.00      ( ~ r2_hidden(sK6,k1_tarski(sK6)) | sK6 = sK6 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1828]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1050,plain,
% 2.73/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_476]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1051,plain,
% 2.73/1.00      ( sK5 != k1_xboole_0
% 2.73/1.00      | k1_xboole_0 = sK5
% 2.73/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1050]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_11,plain,
% 2.73/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_57,plain,
% 2.73/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_12,plain,
% 2.73/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.73/1.00      | k1_xboole_0 = X1
% 2.73/1.00      | k1_xboole_0 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_56,plain,
% 2.73/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.73/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_25,negated_conjecture,
% 2.73/1.00      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 2.73/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(contradiction,plain,
% 2.73/1.00      ( $false ),
% 2.73/1.00      inference(minisat,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3160,c_3146,c_3022,c_3021,c_1722,c_1433,c_1435,c_1065,
% 2.73/1.00                 c_1051,c_292,c_57,c_56,c_43,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.009
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.01
% 2.73/1.00  total_time:                             0.12
% 2.73/1.00  num_of_symbols:                         48
% 2.73/1.00  num_of_terms:                           3779
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    22
% 2.73/1.00  num_of_sem_filtered_clauses:            1
% 2.73/1.00  num_of_subtypes:                        0
% 2.73/1.00  monotx_restored_types:                  0
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       99
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        19
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        4
% 2.73/1.00  pred_elim:                              0
% 2.73/1.00  pred_elim_cl:                           0
% 2.73/1.00  pred_elim_cycles:                       3
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            3
% 2.73/1.00  pred_elim_time:                         0.003
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.001
% 2.73/1.00  subtype_inf_time:                       0.
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                26
% 2.73/1.00  conjectures:                            2
% 2.73/1.00  epr:                                    3
% 2.73/1.00  horn:                                   18
% 2.73/1.00  ground:                                 1
% 2.73/1.00  unary:                                  8
% 2.73/1.00  binary:                                 9
% 2.73/1.00  lits:                                   54
% 2.73/1.00  lits_eq:                                27
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                4
% 2.73/1.00  fd_pseudo_cond:                         4
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      23
% 2.73/1.00  prop_fast_solver_calls:                 583
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    1331
% 2.73/1.00  prop_preprocess_simplified:             4902
% 2.73/1.00  prop_fo_subsumed:                       11
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    353
% 2.73/1.00  inst_num_in_passive:                    148
% 2.73/1.00  inst_num_in_active:                     158
% 2.73/1.00  inst_num_in_unprocessed:                47
% 2.73/1.00  inst_num_of_loops:                      210
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          50
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                0
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      52
% 2.73/1.00  inst_num_of_non_proper_insts:           226
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       102
% 2.73/1.00  res_forward_subset_subsumed:            11
% 2.73/1.00  res_backward_subset_subsumed:           0
% 2.73/1.00  res_forward_subsumed:                   0
% 2.73/1.00  res_backward_subsumed:                  0
% 2.73/1.00  res_forward_subsumption_resolution:     0
% 2.73/1.00  res_backward_subsumption_resolution:    0
% 2.73/1.00  res_clause_to_clause_subsumption:       106
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      5
% 2.73/1.00  res_num_eq_res_simplified:              0
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     62
% 2.73/1.00  sup_num_in_active:                      42
% 2.73/1.00  sup_num_in_passive:                     20
% 2.73/1.00  sup_num_of_loops:                       41
% 2.73/1.00  sup_fw_superposition:                   19
% 2.73/1.00  sup_bw_superposition:                   29
% 2.73/1.00  sup_immediate_simplified:               5
% 2.73/1.00  sup_given_eliminated:                   1
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    5
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 2
% 2.73/1.00  sim_bw_subset_subsumed:                 0
% 2.73/1.00  sim_fw_subsumed:                        1
% 2.73/1.00  sim_bw_subsumed:                        1
% 2.73/1.00  sim_fw_subsumption_res:                 0
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      3
% 2.73/1.00  sim_eq_tautology_del:                   5
% 2.73/1.00  sim_eq_res_simp:                        0
% 2.73/1.00  sim_fw_demodulated:                     1
% 2.73/1.00  sim_bw_demodulated:                     1
% 2.73/1.00  sim_light_normalised:                   0
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------
