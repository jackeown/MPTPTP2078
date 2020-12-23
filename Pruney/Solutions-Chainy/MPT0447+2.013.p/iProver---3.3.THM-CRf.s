%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:11 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 248 expanded)
%              Number of clauses        :   68 (  89 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  388 ( 814 expanded)
%              Number of equality atoms :   99 ( 125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK8))
        & r1_tarski(X0,sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(X1))
          & r1_tarski(sK7,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    & r1_tarski(sK7,sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f62,f61])).

fof(f100,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f82,f88])).

fof(f102,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1488,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_31,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1493,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3108,plain,
    ( k2_xboole_0(k1_relat_1(sK7),k2_relat_1(sK7)) = k3_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1488,c_1493])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1507,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1503,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6050,plain,
    ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1503])).

cnf(c_33155,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3108,c_6050])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1490,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_212,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_26,c_24])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_1486,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1504,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3398,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1504])).

cnf(c_11610,plain,
    ( k2_xboole_0(k2_relat_1(sK7),k2_relat_1(sK8)) = k2_relat_1(sK8)
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_3398])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_12113,plain,
    ( k2_xboole_0(k2_relat_1(sK7),k2_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11610,c_40])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1506,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3701,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1506])).

cnf(c_12123,plain,
    ( r1_tarski(X0,k2_relat_1(sK8)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12113,c_3701])).

cnf(c_33675,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k2_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33155,c_12123])).

cnf(c_1489,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3107,plain,
    ( k2_xboole_0(k1_relat_1(sK8),k2_relat_1(sK8)) = k3_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1489,c_1493])).

cnf(c_3706,plain,
    ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3107,c_1506])).

cnf(c_34959,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33675,c_3706])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_207,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_26,c_24])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_1487,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_4636,plain,
    ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3107,c_3701])).

cnf(c_5264,plain,
    ( r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_4636])).

cnf(c_5266,plain,
    ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(sK7,sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5264])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1579,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
    | ~ r1_tarski(X0,k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1741,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(X0,X1))
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
    | ~ r1_tarski(k6_subset_1(X0,X1),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_5143,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)))
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
    | ~ r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_5149,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0))) != iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5143])).

cnf(c_5151,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7))) != iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k3_relat_1(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5149])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1706,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X1)
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2778,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),X0))
    | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_3039,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)))
    | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7))
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_3040,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0))) = iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3039])).

cnf(c_3042,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7))) = iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3040])).

cnf(c_1971,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
    | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_1972,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_1974,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
    | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1557,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1566,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1559,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7))
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1560,plain,
    ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) = iProver_top
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_42,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34959,c_5266,c_5151,c_3042,c_1974,c_1566,c_1560,c_42,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     num_symb
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       true
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 36
% 7.75/1.50  conjectures                             4
% 7.75/1.50  EPR                                     7
% 7.75/1.50  Horn                                    28
% 7.75/1.50  unary                                   8
% 7.75/1.50  binary                                  14
% 7.75/1.50  lits                                    79
% 7.75/1.50  lits eq                                 16
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 1
% 7.75/1.50  fd_pseudo_cond                          8
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Schedule dynamic 5 is on 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     none
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       false
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f21,conjecture,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f22,negated_conjecture,(
% 7.75/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.75/1.50    inference(negated_conjecture,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.75/1.50    inference(flattening,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK8)) & r1_tarski(X0,sK8) & v1_relat_1(sK8))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK7),k3_relat_1(X1)) & r1_tarski(sK7,X1) & v1_relat_1(X1)) & v1_relat_1(sK7))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    (~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) & r1_tarski(sK7,sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f62,f61])).
% 7.75/1.50  
% 7.75/1.50  fof(f100,plain,(
% 7.75/1.50    v1_relat_1(sK7)),
% 7.75/1.50    inference(cnf_transformation,[],[f63])).
% 7.75/1.50  
% 7.75/1.50  fof(f18,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f96,plain,(
% 7.75/1.50    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(flattening,[],[f48])).
% 7.75/1.50  
% 7.75/1.50  fof(f75,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.75/1.50    inference(cnf_transformation,[],[f49])).
% 7.75/1.50  
% 7.75/1.50  fof(f117,plain,(
% 7.75/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.75/1.50    inference(equality_resolution,[],[f75])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f82,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f88,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f111,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f82,f88])).
% 7.75/1.50  
% 7.75/1.50  fof(f102,plain,(
% 7.75/1.50    r1_tarski(sK7,sK8)),
% 7.75/1.50    inference(cnf_transformation,[],[f63])).
% 7.75/1.50  
% 7.75/1.50  fof(f20,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f99,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f91,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f15,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f90,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f54])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f80,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f101,plain,(
% 7.75/1.50    v1_relat_1(sK8)),
% 7.75/1.50    inference(cnf_transformation,[],[f63])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f78,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f98,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(nnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(rectify,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f65,plain,(
% 7.75/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.75/1.50    inference(nnf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.75/1.50    inference(flattening,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.75/1.50    inference(rectify,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f70,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f107,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k6_subset_1(X0,X1) != X2) )),
% 7.75/1.50    inference(definition_unfolding,[],[f70,f88])).
% 7.75/1.50  
% 7.75/1.50  fof(f113,plain,(
% 7.75/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.75/1.50    inference(equality_resolution,[],[f107])).
% 7.75/1.50  
% 7.75/1.50  fof(f67,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f103,plain,(
% 7.75/1.50    ~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))),
% 7.75/1.50    inference(cnf_transformation,[],[f63])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_38,negated_conjecture,
% 7.75/1.50      ( v1_relat_1(sK7) ),
% 7.75/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1488,plain,
% 7.75/1.50      ( v1_relat_1(sK7) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_31,plain,
% 7.75/1.50      ( ~ v1_relat_1(X0)
% 7.75/1.50      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1493,plain,
% 7.75/1.50      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3108,plain,
% 7.75/1.50      ( k2_xboole_0(k1_relat_1(sK7),k2_relat_1(sK7)) = k3_relat_1(sK7) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1488,c_1493]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_13,plain,
% 7.75/1.50      ( r1_tarski(X0,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1507,plain,
% 7.75/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.75/1.50      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1503,plain,
% 7.75/1.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.75/1.50      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6050,plain,
% 7.75/1.50      ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1507,c_1503]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33155,plain,
% 7.75/1.50      ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k2_relat_1(sK7)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3108,c_6050]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_36,negated_conjecture,
% 7.75/1.50      ( r1_tarski(sK7,sK8) ),
% 7.75/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1490,plain,
% 7.75/1.50      ( r1_tarski(sK7,sK8) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X0)
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_26,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_212,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.75/1.50      | ~ r1_tarski(X0,X1)
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_33,c_26,c_24]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_213,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_212]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1486,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.75/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1504,plain,
% 7.75/1.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3398,plain,
% 7.75/1.50      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
% 7.75/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1486,c_1504]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11610,plain,
% 7.75/1.50      ( k2_xboole_0(k2_relat_1(sK7),k2_relat_1(sK8)) = k2_relat_1(sK8)
% 7.75/1.50      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1490,c_3398]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_37,negated_conjecture,
% 7.75/1.50      ( v1_relat_1(sK8) ),
% 7.75/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_40,plain,
% 7.75/1.50      ( v1_relat_1(sK8) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12113,plain,
% 7.75/1.50      ( k2_xboole_0(k2_relat_1(sK7),k2_relat_1(sK8)) = k2_relat_1(sK8) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_11610,c_40]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1506,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3701,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_0,c_1506]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12123,plain,
% 7.75/1.50      ( r1_tarski(X0,k2_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_12113,c_3701]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33675,plain,
% 7.75/1.50      ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k2_relat_1(sK8)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_33155,c_12123]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1489,plain,
% 7.75/1.50      ( v1_relat_1(sK8) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3107,plain,
% 7.75/1.50      ( k2_xboole_0(k1_relat_1(sK8),k2_relat_1(sK8)) = k3_relat_1(sK8) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1489,c_1493]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3706,plain,
% 7.75/1.50      ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(X0,k2_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3107,c_1506]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34959,plain,
% 7.75/1.50      ( r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k3_relat_1(sK8)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_33675,c_3706]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X0)
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_207,plain,
% 7.75/1.50      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.75/1.50      | ~ r1_tarski(X0,X1)
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_34,c_26,c_24]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_208,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X1) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_207]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1487,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4636,plain,
% 7.75/1.50      ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(X0,k1_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3107,c_3701]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5264,plain,
% 7.75/1.50      ( r1_tarski(X0,sK8) != iProver_top
% 7.75/1.50      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1487,c_4636]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5266,plain,
% 7.75/1.50      ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(sK7,sK8) != iProver_top
% 7.75/1.50      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_5264]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1579,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
% 7.75/1.50      | ~ r1_tarski(X0,k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1741,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(X0,X1))
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
% 7.75/1.50      | ~ r1_tarski(k6_subset_1(X0,X1),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1579]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5143,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)))
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
% 7.75/1.50      | ~ r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1741]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5149,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0))) != iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)),k3_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_5143]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5151,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7))) != iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r1_tarski(k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7)),k3_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_5149]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,X1)
% 7.75/1.50      | r2_hidden(X0,X2)
% 7.75/1.50      | r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1706,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X1)
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(X0,X1)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2778,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),X0)
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),X0))
% 7.75/1.50      | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1706]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3039,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0)))
% 7.75/1.50      | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7))
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2778]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3040,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(X0))) = iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) != iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_3039]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3042,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k6_subset_1(k3_relat_1(sK7),k1_relat_1(sK7))) = iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) != iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(sK7)) = iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_3040]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1971,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
% 7.75/1.50      | ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0))
% 7.75/1.50      | ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1579]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1972,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(X0)) != iProver_top
% 7.75/1.50      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1974,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) = iProver_top
% 7.75/1.50      | r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k1_relat_1(sK7)) != iProver_top
% 7.75/1.50      | r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1972]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1557,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8))
% 7.75/1.50      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1566,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK8)) != iProver_top
% 7.75/1.50      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1559,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7))
% 7.75/1.50      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1560,plain,
% 7.75/1.50      ( r2_hidden(sK0(k3_relat_1(sK7),k3_relat_1(sK8)),k3_relat_1(sK7)) = iProver_top
% 7.75/1.50      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35,negated_conjecture,
% 7.75/1.50      ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_42,plain,
% 7.75/1.50      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_41,plain,
% 7.75/1.50      ( r1_tarski(sK7,sK8) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_34959,c_5266,c_5151,c_3042,c_1974,c_1566,c_1560,c_42,
% 7.75/1.50                 c_41,c_40]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ General
% 7.75/1.50  
% 7.75/1.50  abstr_ref_over_cycles:                  0
% 7.75/1.50  abstr_ref_under_cycles:                 0
% 7.75/1.50  gc_basic_clause_elim:                   0
% 7.75/1.50  forced_gc_time:                         0
% 7.75/1.50  parsing_time:                           0.01
% 7.75/1.50  unif_index_cands_time:                  0.
% 7.75/1.50  unif_index_add_time:                    0.
% 7.75/1.50  orderings_time:                         0.
% 7.75/1.50  out_proof_time:                         0.016
% 7.75/1.50  total_time:                             0.843
% 7.75/1.50  num_of_symbols:                         53
% 7.75/1.50  num_of_terms:                           40738
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing
% 7.75/1.50  
% 7.75/1.50  num_of_splits:                          0
% 7.75/1.50  num_of_split_atoms:                     0
% 7.75/1.50  num_of_reused_defs:                     0
% 7.75/1.50  num_eq_ax_congr_red:                    50
% 7.75/1.50  num_of_sem_filtered_clauses:            1
% 7.75/1.50  num_of_subtypes:                        0
% 7.75/1.50  monotx_restored_types:                  0
% 7.75/1.50  sat_num_of_epr_types:                   0
% 7.75/1.50  sat_num_of_non_cyclic_types:            0
% 7.75/1.50  sat_guarded_non_collapsed_types:        0
% 7.75/1.50  num_pure_diseq_elim:                    0
% 7.75/1.50  simp_replaced_by:                       0
% 7.75/1.50  res_preprocessed:                       167
% 7.75/1.50  prep_upred:                             0
% 7.75/1.50  prep_unflattend:                        0
% 7.75/1.50  smt_new_axioms:                         0
% 7.75/1.50  pred_elim_cands:                        3
% 7.75/1.50  pred_elim:                              1
% 7.75/1.50  pred_elim_cl:                           2
% 7.75/1.50  pred_elim_cycles:                       3
% 7.75/1.50  merged_defs:                            10
% 7.75/1.50  merged_defs_ncl:                        0
% 7.75/1.50  bin_hyper_res:                          11
% 7.75/1.50  prep_cycles:                            4
% 7.75/1.50  pred_elim_time:                         0.
% 7.75/1.50  splitting_time:                         0.
% 7.75/1.50  sem_filter_time:                        0.
% 7.75/1.50  monotx_time:                            0.
% 7.75/1.50  subtype_inf_time:                       0.
% 7.75/1.50  
% 7.75/1.50  ------ Problem properties
% 7.75/1.50  
% 7.75/1.50  clauses:                                36
% 7.75/1.50  conjectures:                            4
% 7.75/1.50  epr:                                    7
% 7.75/1.50  horn:                                   28
% 7.75/1.50  ground:                                 4
% 7.75/1.50  unary:                                  8
% 7.75/1.50  binary:                                 14
% 7.75/1.50  lits:                                   79
% 7.75/1.50  lits_eq:                                16
% 7.75/1.50  fd_pure:                                0
% 7.75/1.50  fd_pseudo:                              0
% 7.75/1.50  fd_cond:                                1
% 7.75/1.50  fd_pseudo_cond:                         8
% 7.75/1.50  ac_symbols:                             0
% 7.75/1.50  
% 7.75/1.50  ------ Propositional Solver
% 7.75/1.50  
% 7.75/1.50  prop_solver_calls:                      31
% 7.75/1.50  prop_fast_solver_calls:                 1190
% 7.75/1.50  smt_solver_calls:                       0
% 7.75/1.50  smt_fast_solver_calls:                  0
% 7.75/1.50  prop_num_of_clauses:                    14264
% 7.75/1.50  prop_preprocess_simplified:             24104
% 7.75/1.50  prop_fo_subsumed:                       9
% 7.75/1.50  prop_solver_time:                       0.
% 7.75/1.50  smt_solver_time:                        0.
% 7.75/1.50  smt_fast_solver_time:                   0.
% 7.75/1.50  prop_fast_solver_time:                  0.
% 7.75/1.50  prop_unsat_core_time:                   0.001
% 7.75/1.50  
% 7.75/1.50  ------ QBF
% 7.75/1.50  
% 7.75/1.50  qbf_q_res:                              0
% 7.75/1.50  qbf_num_tautologies:                    0
% 7.75/1.50  qbf_prep_cycles:                        0
% 7.75/1.50  
% 7.75/1.50  ------ BMC1
% 7.75/1.50  
% 7.75/1.50  bmc1_current_bound:                     -1
% 7.75/1.50  bmc1_last_solved_bound:                 -1
% 7.75/1.50  bmc1_unsat_core_size:                   -1
% 7.75/1.50  bmc1_unsat_core_parents_size:           -1
% 7.75/1.50  bmc1_merge_next_fun:                    0
% 7.75/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation
% 7.75/1.50  
% 7.75/1.50  inst_num_of_clauses:                    3023
% 7.75/1.50  inst_num_in_passive:                    871
% 7.75/1.50  inst_num_in_active:                     988
% 7.75/1.50  inst_num_in_unprocessed:                1164
% 7.75/1.50  inst_num_of_loops:                      1150
% 7.75/1.50  inst_num_of_learning_restarts:          0
% 7.75/1.50  inst_num_moves_active_passive:          161
% 7.75/1.50  inst_lit_activity:                      0
% 7.75/1.50  inst_lit_activity_moves:                0
% 7.75/1.50  inst_num_tautologies:                   0
% 7.75/1.50  inst_num_prop_implied:                  0
% 7.75/1.50  inst_num_existing_simplified:           0
% 7.75/1.50  inst_num_eq_res_simplified:             0
% 7.75/1.50  inst_num_child_elim:                    0
% 7.75/1.50  inst_num_of_dismatching_blockings:      6479
% 7.75/1.50  inst_num_of_non_proper_insts:           4133
% 7.75/1.50  inst_num_of_duplicates:                 0
% 7.75/1.50  inst_inst_num_from_inst_to_res:         0
% 7.75/1.50  inst_dismatching_checking_time:         0.
% 7.75/1.50  
% 7.75/1.50  ------ Resolution
% 7.75/1.50  
% 7.75/1.50  res_num_of_clauses:                     0
% 7.75/1.50  res_num_in_passive:                     0
% 7.75/1.50  res_num_in_active:                      0
% 7.75/1.50  res_num_of_loops:                       171
% 7.75/1.50  res_forward_subset_subsumed:            177
% 7.75/1.50  res_backward_subset_subsumed:           0
% 7.75/1.50  res_forward_subsumed:                   0
% 7.75/1.50  res_backward_subsumed:                  0
% 7.75/1.50  res_forward_subsumption_resolution:     0
% 7.75/1.50  res_backward_subsumption_resolution:    0
% 7.75/1.50  res_clause_to_clause_subsumption:       5350
% 7.75/1.50  res_orphan_elimination:                 0
% 7.75/1.50  res_tautology_del:                      163
% 7.75/1.50  res_num_eq_res_simplified:              0
% 7.75/1.50  res_num_sel_changes:                    0
% 7.75/1.50  res_moves_from_active_to_pass:          0
% 7.75/1.50  
% 7.75/1.50  ------ Superposition
% 7.75/1.50  
% 7.75/1.50  sup_time_total:                         0.
% 7.75/1.50  sup_time_generating:                    0.
% 7.75/1.50  sup_time_sim_full:                      0.
% 7.75/1.50  sup_time_sim_immed:                     0.
% 7.75/1.50  
% 7.75/1.50  sup_num_of_clauses:                     1061
% 7.75/1.50  sup_num_in_active:                      198
% 7.75/1.50  sup_num_in_passive:                     863
% 7.75/1.50  sup_num_of_loops:                       228
% 7.75/1.50  sup_fw_superposition:                   857
% 7.75/1.50  sup_bw_superposition:                   1418
% 7.75/1.50  sup_immediate_simplified:               384
% 7.75/1.50  sup_given_eliminated:                   4
% 7.75/1.50  comparisons_done:                       0
% 7.75/1.50  comparisons_avoided:                    1
% 7.75/1.50  
% 7.75/1.50  ------ Simplifications
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  sim_fw_subset_subsumed:                 89
% 7.75/1.50  sim_bw_subset_subsumed:                 12
% 7.75/1.50  sim_fw_subsumed:                        192
% 7.75/1.50  sim_bw_subsumed:                        22
% 7.75/1.50  sim_fw_subsumption_res:                 0
% 7.75/1.50  sim_bw_subsumption_res:                 0
% 7.75/1.50  sim_tautology_del:                      93
% 7.75/1.50  sim_eq_tautology_del:                   13
% 7.75/1.50  sim_eq_res_simp:                        1
% 7.75/1.50  sim_fw_demodulated:                     51
% 7.75/1.50  sim_bw_demodulated:                     22
% 7.75/1.50  sim_light_normalised:                   76
% 7.75/1.50  sim_joinable_taut:                      0
% 7.75/1.50  sim_joinable_simp:                      0
% 7.75/1.50  sim_ac_normalised:                      0
% 7.75/1.50  sim_smt_subsumption:                    0
% 7.75/1.50  
%------------------------------------------------------------------------------
