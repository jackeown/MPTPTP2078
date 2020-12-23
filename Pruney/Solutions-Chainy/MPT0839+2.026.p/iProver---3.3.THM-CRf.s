%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:48 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 258 expanded)
%              Number of clauses        :   58 (  77 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 ( 938 expanded)
%              Number of equality atoms :   72 ( 146 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
          | ~ m1_subset_1(X3,sK5) )
      & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
        | ~ m1_subset_1(X3,sK5) )
    & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f40])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1979,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1287,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_8,c_24])).

cnf(c_1437,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1287])).

cnf(c_1870,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
    inference(resolution,[status(thm)],[c_6,c_1437])).

cnf(c_5086,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),sK5)
    | k1_relat_1(sK6) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_1870])).

cnf(c_486,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_5481,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),sK5)
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK6),X1) ),
    inference(resolution,[status(thm)],[c_5086,c_486])).

cnf(c_7221,plain,
    ( r2_hidden(sK1(sK6,sK6),sK6)
    | r2_hidden(sK1(sK6,sK6),sK5)
    | r1_tarski(k1_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_5481,c_1287])).

cnf(c_8093,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK6),sK6)
    | r2_hidden(sK1(sK6,sK6),sK5) ),
    inference(resolution,[status(thm)],[c_1979,c_7221])).

cnf(c_1043,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1046,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1923,plain,
    ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1043,c_1046])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1044,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2246,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1923,c_1044])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2246])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2270,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_1870,c_13])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2289,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),X0),sK5)
    | r1_tarski(k1_relat_1(sK6),X0) ),
    inference(resolution,[status(thm)],[c_2270,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2433,plain,
    ( r1_tarski(k1_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_2289,c_0])).

cnf(c_8073,plain,
    ( m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_1979,c_2433])).

cnf(c_8295,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8093,c_2258,c_8073])).

cnf(c_8538,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) ),
    inference(resolution,[status(thm)],[c_8295,c_1])).

cnf(c_8540,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8538])).

cnf(c_5188,plain,
    ( r2_hidden(sK1(sK6,X0),X1)
    | ~ r2_hidden(sK1(sK6,X0),k1_relat_1(sK6))
    | ~ r1_tarski(k1_relat_1(sK6),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5193,plain,
    ( ~ r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5188])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2238,plain,
    ( r1_tarski(k1_xboole_0,sK1(sK6,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1830,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK2(sK6,k1_xboole_0)),sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1571,plain,
    ( ~ r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1(sK6,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_485,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1394,plain,
    ( k2_relat_1(sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1395,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1389,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK2(sK6,k1_xboole_0)),sK6)
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1261,plain,
    ( k2_relset_1(sK5,sK4,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1347,plain,
    ( k2_relset_1(sK5,sK4,sK6) != k2_relat_1(sK6)
    | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6)
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1299,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_484,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_507,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8540,c_5193,c_2238,c_1830,c_1571,c_1395,c_1389,c_1347,c_1299,c_1268,c_1244,c_507,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:08:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.14/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.01  
% 3.14/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/1.01  
% 3.14/1.01  ------  iProver source info
% 3.14/1.01  
% 3.14/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.14/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/1.01  git: non_committed_changes: false
% 3.14/1.01  git: last_make_outside_of_git: false
% 3.14/1.01  
% 3.14/1.01  ------ 
% 3.14/1.01  ------ Parsing...
% 3.14/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.01  ------ Proving...
% 3.14/1.01  ------ Problem Properties 
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  clauses                                 25
% 3.14/1.01  conjectures                             3
% 3.14/1.01  EPR                                     3
% 3.14/1.01  Horn                                    23
% 3.14/1.01  unary                                   5
% 3.14/1.01  binary                                  13
% 3.14/1.01  lits                                    52
% 3.14/1.01  lits eq                                 11
% 3.14/1.01  fd_pure                                 0
% 3.14/1.01  fd_pseudo                               0
% 3.14/1.01  fd_cond                                 0
% 3.14/1.01  fd_pseudo_cond                          2
% 3.14/1.01  AC symbols                              0
% 3.14/1.01  
% 3.14/1.01  ------ Input Options Time Limit: Unbounded
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  ------ 
% 3.14/1.01  Current options:
% 3.14/1.01  ------ 
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  ------ Proving...
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  % SZS status Theorem for theBenchmark.p
% 3.14/1.01  
% 3.14/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.01  
% 3.14/1.01  fof(f5,axiom,(
% 3.14/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f17,plain,(
% 3.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.14/1.01    inference(ennf_transformation,[],[f5])).
% 3.14/1.01  
% 3.14/1.01  fof(f18,plain,(
% 3.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.14/1.01    inference(flattening,[],[f17])).
% 3.14/1.01  
% 3.14/1.01  fof(f51,plain,(
% 3.14/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f18])).
% 3.14/1.01  
% 3.14/1.01  fof(f4,axiom,(
% 3.14/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f32,plain,(
% 3.14/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.14/1.01    inference(nnf_transformation,[],[f4])).
% 3.14/1.01  
% 3.14/1.01  fof(f50,plain,(
% 3.14/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f32])).
% 3.14/1.01  
% 3.14/1.01  fof(f6,axiom,(
% 3.14/1.01    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f33,plain,(
% 3.14/1.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.14/1.01    inference(nnf_transformation,[],[f6])).
% 3.14/1.01  
% 3.14/1.01  fof(f34,plain,(
% 3.14/1.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.14/1.01    inference(rectify,[],[f33])).
% 3.14/1.01  
% 3.14/1.01  fof(f37,plain,(
% 3.14/1.01    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 3.14/1.01    introduced(choice_axiom,[])).
% 3.14/1.01  
% 3.14/1.01  fof(f36,plain,(
% 3.14/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 3.14/1.01    introduced(choice_axiom,[])).
% 3.14/1.01  
% 3.14/1.01  fof(f35,plain,(
% 3.14/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f38,plain,(
% 3.14/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 3.14/1.02  
% 3.14/1.02  fof(f54,plain,(
% 3.14/1.02    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f38])).
% 3.14/1.02  
% 3.14/1.02  fof(f3,axiom,(
% 3.14/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f30,plain,(
% 3.14/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.14/1.02    inference(nnf_transformation,[],[f3])).
% 3.14/1.02  
% 3.14/1.02  fof(f31,plain,(
% 3.14/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.14/1.02    inference(flattening,[],[f30])).
% 3.14/1.02  
% 3.14/1.02  fof(f46,plain,(
% 3.14/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f31])).
% 3.14/1.02  
% 3.14/1.02  fof(f1,axiom,(
% 3.14/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f16,plain,(
% 3.14/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.14/1.02    inference(ennf_transformation,[],[f1])).
% 3.14/1.02  
% 3.14/1.02  fof(f26,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(nnf_transformation,[],[f16])).
% 3.14/1.02  
% 3.14/1.02  fof(f27,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(rectify,[],[f26])).
% 3.14/1.02  
% 3.14/1.02  fof(f28,plain,(
% 3.14/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f29,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.14/1.02  
% 3.14/1.02  fof(f42,plain,(
% 3.14/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f29])).
% 3.14/1.02  
% 3.14/1.02  fof(f49,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f32])).
% 3.14/1.02  
% 3.14/1.02  fof(f13,conjecture,(
% 3.14/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f14,negated_conjecture,(
% 3.14/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 3.14/1.02    inference(negated_conjecture,[],[f13])).
% 3.14/1.02  
% 3.14/1.02  fof(f15,plain,(
% 3.14/1.02    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 3.14/1.02    inference(pure_predicate_removal,[],[f14])).
% 3.14/1.02  
% 3.14/1.02  fof(f24,plain,(
% 3.14/1.02    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.14/1.02    inference(ennf_transformation,[],[f15])).
% 3.14/1.02  
% 3.14/1.02  fof(f25,plain,(
% 3.14/1.02    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.14/1.02    inference(flattening,[],[f24])).
% 3.14/1.02  
% 3.14/1.02  fof(f40,plain,(
% 3.14/1.02    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f41,plain,(
% 3.14/1.02    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f40])).
% 3.14/1.02  
% 3.14/1.02  fof(f64,plain,(
% 3.14/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f11,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f22,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f11])).
% 3.14/1.02  
% 3.14/1.02  fof(f62,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f22])).
% 3.14/1.02  
% 3.14/1.02  fof(f66,plain,(
% 3.14/1.02    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f52,plain,(
% 3.14/1.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.14/1.02    inference(cnf_transformation,[],[f38])).
% 3.14/1.02  
% 3.14/1.02  fof(f68,plain,(
% 3.14/1.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.14/1.02    inference(equality_resolution,[],[f52])).
% 3.14/1.02  
% 3.14/1.02  fof(f43,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f29])).
% 3.14/1.02  
% 3.14/1.02  fof(f44,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f29])).
% 3.14/1.02  
% 3.14/1.02  fof(f2,axiom,(
% 3.14/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f45,plain,(
% 3.14/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f2])).
% 3.14/1.02  
% 3.14/1.02  fof(f53,plain,(
% 3.14/1.02    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.14/1.02    inference(cnf_transformation,[],[f38])).
% 3.14/1.02  
% 3.14/1.02  fof(f67,plain,(
% 3.14/1.02    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.14/1.02    inference(equality_resolution,[],[f53])).
% 3.14/1.02  
% 3.14/1.02  fof(f9,axiom,(
% 3.14/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f20,plain,(
% 3.14/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.14/1.02    inference(ennf_transformation,[],[f9])).
% 3.14/1.02  
% 3.14/1.02  fof(f60,plain,(
% 3.14/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f20])).
% 3.14/1.02  
% 3.14/1.02  fof(f8,axiom,(
% 3.14/1.02    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f19,plain,(
% 3.14/1.02    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.14/1.02    inference(ennf_transformation,[],[f8])).
% 3.14/1.02  
% 3.14/1.02  fof(f39,plain,(
% 3.14/1.02    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.14/1.02    inference(nnf_transformation,[],[f19])).
% 3.14/1.02  
% 3.14/1.02  fof(f58,plain,(
% 3.14/1.02    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f39])).
% 3.14/1.02  
% 3.14/1.02  fof(f12,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f23,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f12])).
% 3.14/1.02  
% 3.14/1.02  fof(f63,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f23])).
% 3.14/1.02  
% 3.14/1.02  fof(f10,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f21,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f10])).
% 3.14/1.02  
% 3.14/1.02  fof(f61,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f21])).
% 3.14/1.02  
% 3.14/1.02  fof(f65,plain,(
% 3.14/1.02    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  cnf(c_9,plain,
% 3.14/1.02      ( m1_subset_1(X0,X1)
% 3.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.14/1.02      | ~ r2_hidden(X0,X2) ),
% 3.14/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_7,plain,
% 3.14/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1979,plain,
% 3.14/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_tarski(X2,X1) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_11,plain,
% 3.14/1.02      ( r2_hidden(sK1(X0,X1),X1)
% 3.14/1.02      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 3.14/1.02      | k1_relat_1(X0) = X1 ),
% 3.14/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_6,plain,
% 3.14/1.02      ( r2_hidden(X0,X1)
% 3.14/1.02      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.14/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.14/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_24,negated_conjecture,
% 3.14/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 3.14/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1287,plain,
% 3.14/1.02      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_8,c_24]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1437,plain,
% 3.14/1.02      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4)) | ~ r2_hidden(X0,sK6) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_2,c_1287]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1870,plain,
% 3.14/1.02      ( r2_hidden(X0,sK5) | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_6,c_1437]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5086,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,X0),X0)
% 3.14/1.02      | r2_hidden(sK1(sK6,X0),sK5)
% 3.14/1.02      | k1_relat_1(sK6) = X0 ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_11,c_1870]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_486,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.14/1.02      theory(equality) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5481,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,X0),X0)
% 3.14/1.02      | r2_hidden(sK1(sK6,X0),sK5)
% 3.14/1.02      | ~ r1_tarski(X0,X1)
% 3.14/1.02      | r1_tarski(k1_relat_1(sK6),X1) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_5086,c_486]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_7221,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,sK6),sK6)
% 3.14/1.02      | r2_hidden(sK1(sK6,sK6),sK5)
% 3.14/1.02      | r1_tarski(k1_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_5481,c_1287]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8093,plain,
% 3.14/1.02      ( m1_subset_1(X0,k2_zfmisc_1(sK5,sK4))
% 3.14/1.02      | ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.14/1.02      | r2_hidden(sK1(sK6,sK6),sK6)
% 3.14/1.02      | r2_hidden(sK1(sK6,sK6),sK5) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_1979,c_7221]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1043,plain,
% 3.14/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_20,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1046,plain,
% 3.14/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1923,plain,
% 3.14/1.02      ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1043,c_1046]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_22,negated_conjecture,
% 3.14/1.02      ( ~ m1_subset_1(X0,sK5)
% 3.14/1.02      | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
% 3.14/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1044,plain,
% 3.14/1.02      ( m1_subset_1(X0,sK5) != iProver_top
% 3.14/1.02      | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2246,plain,
% 3.14/1.02      ( m1_subset_1(X0,sK5) != iProver_top
% 3.14/1.02      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_1923,c_1044]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2258,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,sK5) | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 3.14/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2246]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_13,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.14/1.02      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2270,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(X0,sK5) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_1870,c_13]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1,plain,
% 3.14/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2289,plain,
% 3.14/1.02      ( r2_hidden(sK0(k1_relat_1(sK6),X0),sK5)
% 3.14/1.02      | r1_tarski(k1_relat_1(sK6),X0) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_2270,c_1]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_0,plain,
% 3.14/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2433,plain,
% 3.14/1.02      ( r1_tarski(k1_relat_1(sK6),sK5) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_2289,c_0]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8073,plain,
% 3.14/1.02      ( m1_subset_1(X0,sK5) | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_1979,c_2433]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8295,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_8093,c_2258,c_8073]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8538,plain,
% 3.14/1.02      ( r1_tarski(k1_relat_1(sK6),X0) ),
% 3.14/1.02      inference(resolution,[status(thm)],[c_8295,c_1]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_8540,plain,
% 3.14/1.02      ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_8538]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5188,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,X0),X1)
% 3.14/1.02      | ~ r2_hidden(sK1(sK6,X0),k1_relat_1(sK6))
% 3.14/1.02      | ~ r1_tarski(k1_relat_1(sK6),X1) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5193,plain,
% 3.14/1.02      ( ~ r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6))
% 3.14/1.02      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
% 3.14/1.02      | ~ r1_tarski(k1_relat_1(sK6),k1_xboole_0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_5188]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3,plain,
% 3.14/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2238,plain,
% 3.14/1.02      ( r1_tarski(k1_xboole_0,sK1(sK6,k1_xboole_0)) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_12,plain,
% 3.14/1.02      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1830,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6))
% 3.14/1.02      | ~ r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK2(sK6,k1_xboole_0)),sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_18,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1571,plain,
% 3.14/1.02      ( ~ r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
% 3.14/1.02      | ~ r1_tarski(k1_xboole_0,sK1(sK6,k1_xboole_0)) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_485,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1394,plain,
% 3.14/1.02      ( k2_relat_1(sK6) != X0
% 3.14/1.02      | k1_xboole_0 != X0
% 3.14/1.02      | k1_xboole_0 = k2_relat_1(sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_485]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1395,plain,
% 3.14/1.02      ( k2_relat_1(sK6) != k1_xboole_0
% 3.14/1.02      | k1_xboole_0 = k2_relat_1(sK6)
% 3.14/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_1394]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1389,plain,
% 3.14/1.02      ( r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0)
% 3.14/1.02      | r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK2(sK6,k1_xboole_0)),sK6)
% 3.14/1.02      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1261,plain,
% 3.14/1.02      ( k2_relset_1(sK5,sK4,sK6) != X0
% 3.14/1.02      | k1_xboole_0 != X0
% 3.14/1.02      | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_485]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1347,plain,
% 3.14/1.02      ( k2_relset_1(sK5,sK4,sK6) != k2_relat_1(sK6)
% 3.14/1.02      | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6)
% 3.14/1.02      | k1_xboole_0 != k2_relat_1(sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_1261]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_17,plain,
% 3.14/1.02      ( ~ v1_relat_1(X0)
% 3.14/1.02      | k2_relat_1(X0) = k1_xboole_0
% 3.14/1.02      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.14/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1299,plain,
% 3.14/1.02      ( ~ v1_relat_1(sK6)
% 3.14/1.02      | k2_relat_1(sK6) = k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK6) != k1_xboole_0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_21,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1268,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.14/1.02      | k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_19,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | v1_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1244,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.14/1.02      | v1_relat_1(sK6) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_19]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_484,plain,( X0 = X0 ),theory(equality) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_507,plain,
% 3.14/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_484]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_23,negated_conjecture,
% 3.14/1.02      ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
% 3.14/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(contradiction,plain,
% 3.14/1.02      ( $false ),
% 3.14/1.02      inference(minisat,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_8540,c_5193,c_2238,c_1830,c_1571,c_1395,c_1389,c_1347,
% 3.14/1.02                 c_1299,c_1268,c_1244,c_507,c_23,c_24]) ).
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.02  
% 3.14/1.02  ------                               Statistics
% 3.14/1.02  
% 3.14/1.02  ------ Selected
% 3.14/1.02  
% 3.14/1.02  total_time:                             0.219
% 3.14/1.02  
%------------------------------------------------------------------------------
