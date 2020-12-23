%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:55 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 329 expanded)
%              Number of clauses        :   68 ( 122 expanded)
%              Number of leaves         :   21 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  349 (1080 expanded)
%              Number of equality atoms :  118 ( 301 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,
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

fof(f42,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
        | ~ m1_subset_1(X3,sK5) )
    & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f41])).

fof(f66,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1130,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1138,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1128,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1124,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2215,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(X1,k4_tarski(X0,sK3(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1128,c_1124])).

cnf(c_3872,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_2215])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3873,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3872,c_17])).

cnf(c_3878,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_3873])).

cnf(c_3882,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3878,c_17])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1132,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2999,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1132])).

cnf(c_4810,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK1(k1_xboole_0,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3882,c_2999])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1120,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1123,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1966,plain,
    ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1120,c_1123])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1121,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2368,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1966,c_1121])).

cnf(c_4029,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK1(k1_xboole_0,k1_relat_1(sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3882,c_2368])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_523,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_548,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_524,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1340,plain,
    ( k2_relset_1(sK5,sK4,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1420,plain,
    ( k2_relset_1(sK5,sK4,sK6) != k2_relat_1(sK6)
    | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6)
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_1483,plain,
    ( k2_relat_1(sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1484,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1672,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1673,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1672])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1499,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1133])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_186])).

cnf(c_1119,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_3768,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_1119])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1127,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3783,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3768,c_1127])).

cnf(c_4291,plain,
    ( m1_subset_1(sK1(k1_xboole_0,k1_relat_1(sK6)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_25,c_24,c_548,c_1351,c_1420,c_1484,c_1673,c_3783])).

cnf(c_6553,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4810,c_4291])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1376,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

cnf(c_1530,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1376])).

cnf(c_1981,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
    inference(resolution,[status(thm)],[c_6,c_1530])).

cnf(c_2400,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_1981,c_14])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2419,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),X0),sK5)
    | r1_tarski(k1_relat_1(sK6),X0) ),
    inference(resolution,[status(thm)],[c_2400,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2605,plain,
    ( r1_tarski(k1_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_2419,c_0])).

cnf(c_2606,plain,
    ( r1_tarski(k1_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2605])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6553,c_3783,c_2606,c_1673,c_1484,c_1420,c_1351,c_548,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:29:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 2.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.99  
% 2.87/0.99  ------  iProver source info
% 2.87/0.99  
% 2.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.99  git: non_committed_changes: false
% 2.87/0.99  git: last_make_outside_of_git: false
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  ------ Parsing...
% 2.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.99  ------ Proving...
% 2.87/0.99  ------ Problem Properties 
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  clauses                                 26
% 2.87/0.99  conjectures                             3
% 2.87/0.99  EPR                                     4
% 2.87/0.99  Horn                                    24
% 2.87/0.99  unary                                   6
% 2.87/0.99  binary                                  12
% 2.87/0.99  lits                                    54
% 2.87/0.99  lits eq                                 11
% 2.87/0.99  fd_pure                                 0
% 2.87/0.99  fd_pseudo                               0
% 2.87/0.99  fd_cond                                 0
% 2.87/0.99  fd_pseudo_cond                          2
% 2.87/0.99  AC symbols                              0
% 2.87/0.99  
% 2.87/0.99  ------ Input Options Time Limit: Unbounded
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  Current options:
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ Proving...
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  % SZS status Theorem for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  fof(f7,axiom,(
% 2.87/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f34,plain,(
% 2.87/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.87/0.99    inference(nnf_transformation,[],[f7])).
% 2.87/0.99  
% 2.87/0.99  fof(f35,plain,(
% 2.87/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.87/0.99    inference(rectify,[],[f34])).
% 2.87/0.99  
% 2.87/0.99  fof(f38,plain,(
% 2.87/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f37,plain,(
% 2.87/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f36,plain,(
% 2.87/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f39,plain,(
% 2.87/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 2.87/0.99  
% 2.87/0.99  fof(f56,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f39])).
% 2.87/0.99  
% 2.87/0.99  fof(f2,axiom,(
% 2.87/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f46,plain,(
% 2.87/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f2])).
% 2.87/0.99  
% 2.87/0.99  fof(f54,plain,(
% 2.87/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.87/0.99    inference(cnf_transformation,[],[f39])).
% 2.87/0.99  
% 2.87/0.99  fof(f70,plain,(
% 2.87/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.87/0.99    inference(equality_resolution,[],[f54])).
% 2.87/0.99  
% 2.87/0.99  fof(f11,axiom,(
% 2.87/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f22,plain,(
% 2.87/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.87/0.99    inference(ennf_transformation,[],[f11])).
% 2.87/0.99  
% 2.87/0.99  fof(f63,plain,(
% 2.87/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f9,axiom,(
% 2.87/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f59,plain,(
% 2.87/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.87/0.99    inference(cnf_transformation,[],[f9])).
% 2.87/0.99  
% 2.87/0.99  fof(f4,axiom,(
% 2.87/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f33,plain,(
% 2.87/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.87/0.99    inference(nnf_transformation,[],[f4])).
% 2.87/0.99  
% 2.87/0.99  fof(f51,plain,(
% 2.87/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f33])).
% 2.87/0.99  
% 2.87/0.99  fof(f5,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f18,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f5])).
% 2.87/0.99  
% 2.87/0.99  fof(f19,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.87/0.99    inference(flattening,[],[f18])).
% 2.87/0.99  
% 2.87/0.99  fof(f52,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f19])).
% 2.87/0.99  
% 2.87/0.99  fof(f14,conjecture,(
% 2.87/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f15,negated_conjecture,(
% 2.87/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.87/0.99    inference(negated_conjecture,[],[f14])).
% 2.87/0.99  
% 2.87/0.99  fof(f16,plain,(
% 2.87/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 2.87/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.87/0.99  
% 2.87/0.99  fof(f25,plain,(
% 2.87/0.99    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/0.99    inference(ennf_transformation,[],[f16])).
% 2.87/0.99  
% 2.87/0.99  fof(f26,plain,(
% 2.87/0.99    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/0.99    inference(flattening,[],[f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f41,plain,(
% 2.87/0.99    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f42,plain,(
% 2.87/0.99    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f41])).
% 2.87/0.99  
% 2.87/0.99  fof(f66,plain,(
% 2.87/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 2.87/0.99    inference(cnf_transformation,[],[f42])).
% 2.87/0.99  
% 2.87/0.99  fof(f12,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f23,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f12])).
% 2.87/0.99  
% 2.87/0.99  fof(f64,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f23])).
% 2.87/0.99  
% 2.87/0.99  fof(f68,plain,(
% 2.87/0.99    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f42])).
% 2.87/0.99  
% 2.87/0.99  fof(f67,plain,(
% 2.87/0.99    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)),
% 2.87/0.99    inference(cnf_transformation,[],[f42])).
% 2.87/0.99  
% 2.87/0.99  fof(f13,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f24,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f13])).
% 2.87/0.99  
% 2.87/0.99  fof(f65,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f24])).
% 2.87/0.99  
% 2.87/0.99  fof(f10,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f21,plain,(
% 2.87/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f10])).
% 2.87/0.99  
% 2.87/0.99  fof(f40,plain,(
% 2.87/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(nnf_transformation,[],[f21])).
% 2.87/0.99  
% 2.87/0.99  fof(f61,plain,(
% 2.87/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f40])).
% 2.87/0.99  
% 2.87/0.99  fof(f50,plain,(
% 2.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f33])).
% 2.87/0.99  
% 2.87/0.99  fof(f6,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f20,plain,(
% 2.87/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f6])).
% 2.87/0.99  
% 2.87/0.99  fof(f53,plain,(
% 2.87/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f8,axiom,(
% 2.87/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f58,plain,(
% 2.87/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f8])).
% 2.87/0.99  
% 2.87/0.99  fof(f3,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f31,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.87/0.99    inference(nnf_transformation,[],[f3])).
% 2.87/0.99  
% 2.87/0.99  fof(f32,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.87/0.99    inference(flattening,[],[f31])).
% 2.87/0.99  
% 2.87/0.99  fof(f47,plain,(
% 2.87/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f32])).
% 2.87/0.99  
% 2.87/0.99  fof(f1,axiom,(
% 2.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f17,plain,(
% 2.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f1])).
% 2.87/0.99  
% 2.87/0.99  fof(f27,plain,(
% 2.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/0.99    inference(nnf_transformation,[],[f17])).
% 2.87/0.99  
% 2.87/0.99  fof(f28,plain,(
% 2.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/0.99    inference(rectify,[],[f27])).
% 2.87/0.99  
% 2.87/0.99  fof(f29,plain,(
% 2.87/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f30,plain,(
% 2.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.87/0.99  
% 2.87/0.99  fof(f43,plain,(
% 2.87/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f30])).
% 2.87/0.99  
% 2.87/0.99  fof(f44,plain,(
% 2.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f30])).
% 2.87/0.99  
% 2.87/0.99  fof(f45,plain,(
% 2.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f30])).
% 2.87/0.99  
% 2.87/0.99  cnf(c_12,plain,
% 2.87/0.99      ( r2_hidden(sK1(X0,X1),X1)
% 2.87/0.99      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 2.87/0.99      | k1_relat_1(X0) = X1 ),
% 2.87/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1130,plain,
% 2.87/0.99      ( k1_relat_1(X0) = X1
% 2.87/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 2.87/0.99      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3,plain,
% 2.87/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1138,plain,
% 2.87/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_14,plain,
% 2.87/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.87/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1128,plain,
% 2.87/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.87/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_20,plain,
% 2.87/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1124,plain,
% 2.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.87/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2215,plain,
% 2.87/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.87/0.99      | r1_tarski(X1,k4_tarski(X0,sK3(X1,X0))) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1128,c_1124]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3872,plain,
% 2.87/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1138,c_2215]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_17,plain,
% 2.87/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.87/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3873,plain,
% 2.87/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.87/0.99      inference(light_normalisation,[status(thm)],[c_3872,c_17]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3878,plain,
% 2.87/0.99      ( k1_relat_1(k1_xboole_0) = X0
% 2.87/0.99      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1130,c_3873]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3882,plain,
% 2.87/0.99      ( k1_xboole_0 = X0
% 2.87/0.99      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 2.87/0.99      inference(demodulation,[status(thm)],[c_3878,c_17]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_7,plain,
% 2.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1134,plain,
% 2.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.87/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_9,plain,
% 2.87/0.99      ( m1_subset_1(X0,X1)
% 2.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.87/0.99      | ~ r2_hidden(X0,X2) ),
% 2.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1132,plain,
% 2.87/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.87/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2999,plain,
% 2.87/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.87/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.87/0.99      | r1_tarski(X2,X1) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1134,c_1132]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_4810,plain,
% 2.87/0.99      ( k1_xboole_0 = X0
% 2.87/0.99      | m1_subset_1(sK1(k1_xboole_0,X0),X1) = iProver_top
% 2.87/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_3882,c_2999]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_25,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 2.87/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1120,plain,
% 2.87/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_21,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1123,plain,
% 2.87/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1966,plain,
% 2.87/0.99      ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1120,c_1123]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_23,negated_conjecture,
% 2.87/0.99      ( ~ m1_subset_1(X0,sK5)
% 2.87/0.99      | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1121,plain,
% 2.87/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 2.87/0.99      | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2368,plain,
% 2.87/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 2.87/0.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.87/0.99      inference(demodulation,[status(thm)],[c_1966,c_1121]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_4029,plain,
% 2.87/0.99      ( k1_relat_1(sK6) = k1_xboole_0
% 2.87/0.99      | m1_subset_1(sK1(k1_xboole_0,k1_relat_1(sK6)),sK5) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_3882,c_2368]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_24,negated_conjecture,
% 2.87/0.99      ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
% 2.87/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_523,plain,( X0 = X0 ),theory(equality) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_548,plain,
% 2.87/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_523]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_22,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1351,plain,
% 2.87/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.87/0.99      | k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_524,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1340,plain,
% 2.87/0.99      ( k2_relset_1(sK5,sK4,sK6) != X0
% 2.87/0.99      | k1_xboole_0 != X0
% 2.87/0.99      | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_524]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1420,plain,
% 2.87/0.99      ( k2_relset_1(sK5,sK4,sK6) != k2_relat_1(sK6)
% 2.87/0.99      | k1_xboole_0 = k2_relset_1(sK5,sK4,sK6)
% 2.87/0.99      | k1_xboole_0 != k2_relat_1(sK6) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1340]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1483,plain,
% 2.87/0.99      ( k2_relat_1(sK6) != X0
% 2.87/0.99      | k1_xboole_0 != X0
% 2.87/0.99      | k1_xboole_0 = k2_relat_1(sK6) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_524]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1484,plain,
% 2.87/0.99      ( k2_relat_1(sK6) != k1_xboole_0
% 2.87/0.99      | k1_xboole_0 = k2_relat_1(sK6)
% 2.87/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1483]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_19,plain,
% 2.87/0.99      ( ~ v1_relat_1(X0)
% 2.87/0.99      | k2_relat_1(X0) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1672,plain,
% 2.87/0.99      ( ~ v1_relat_1(sK6)
% 2.87/0.99      | k2_relat_1(sK6) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(sK6) != k1_xboole_0 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1673,plain,
% 2.87/0.99      ( k2_relat_1(sK6) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(sK6) != k1_xboole_0
% 2.87/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1672]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_8,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1133,plain,
% 2.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.87/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1499,plain,
% 2.87/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1120,c_1133]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_10,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/0.99      | ~ v1_relat_1(X1)
% 2.87/0.99      | v1_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_185,plain,
% 2.87/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.87/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_186,plain,
% 2.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.87/0.99      inference(renaming,[status(thm)],[c_185]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_234,plain,
% 2.87/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.87/0.99      inference(bin_hyper_res,[status(thm)],[c_10,c_186]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1119,plain,
% 2.87/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.87/0.99      | v1_relat_1(X1) != iProver_top
% 2.87/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3768,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
% 2.87/0.99      | v1_relat_1(sK6) = iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1499,c_1119]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_15,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1127,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3783,plain,
% 2.87/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 2.87/0.99      inference(forward_subsumption_resolution,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_3768,c_1127]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_4291,plain,
% 2.87/0.99      ( m1_subset_1(sK1(k1_xboole_0,k1_relat_1(sK6)),sK5) != iProver_top ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_4029,c_25,c_24,c_548,c_1351,c_1420,c_1484,c_1673,
% 2.87/0.99                 c_3783]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_6553,plain,
% 2.87/0.99      ( k1_relat_1(sK6) = k1_xboole_0
% 2.87/0.99      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_4810,c_4291]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_6,plain,
% 2.87/0.99      ( r2_hidden(X0,X1)
% 2.87/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2,plain,
% 2.87/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.87/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1376,plain,
% 2.87/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_8,c_25]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1530,plain,
% 2.87/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4)) | ~ r2_hidden(X0,sK6) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_2,c_1376]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1981,plain,
% 2.87/0.99      ( r2_hidden(X0,sK5) | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_6,c_1530]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2400,plain,
% 2.87/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(X0,sK5) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_1981,c_14]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1,plain,
% 2.87/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2419,plain,
% 2.87/0.99      ( r2_hidden(sK0(k1_relat_1(sK6),X0),sK5)
% 2.87/0.99      | r1_tarski(k1_relat_1(sK6),X0) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_2400,c_1]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_0,plain,
% 2.87/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2605,plain,
% 2.87/0.99      ( r1_tarski(k1_relat_1(sK6),sK5) ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_2419,c_0]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2606,plain,
% 2.87/0.99      ( r1_tarski(k1_relat_1(sK6),sK5) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2605]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(contradiction,plain,
% 2.87/0.99      ( $false ),
% 2.87/0.99      inference(minisat,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_6553,c_3783,c_2606,c_1673,c_1484,c_1420,c_1351,c_548,
% 2.87/0.99                 c_24,c_25]) ).
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  ------                               Statistics
% 2.87/0.99  
% 2.87/0.99  ------ Selected
% 2.87/0.99  
% 2.87/0.99  total_time:                             0.224
% 2.87/0.99  
%------------------------------------------------------------------------------
