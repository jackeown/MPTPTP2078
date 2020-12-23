%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:01 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  148 (1301 expanded)
%              Number of clauses        :   92 ( 472 expanded)
%              Number of leaves         :   13 ( 227 expanded)
%              Depth                    :   23
%              Number of atoms          :  424 (4882 expanded)
%              Number of equality atoms :  206 (1381 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
        | ~ v1_funct_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).

fof(f58,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_937,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_933,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1581,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_933])).

cnf(c_1605,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_1581])).

cnf(c_1985,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_937,c_1605])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_940,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_179])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_225])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_931,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1333,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_931])).

cnf(c_1445,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_1333])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_124,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_23])).

cnf(c_125,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK1) != X2
    | k1_relat_1(sK1) != X1
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_125])).

cnf(c_381,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_389,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_381,c_15])).

cnf(c_928,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1324,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_928])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_305,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_306,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_307,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1349,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_307])).

cnf(c_932,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1355,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1349,c_932])).

cnf(c_1357,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1355,c_7])).

cnf(c_1446,plain,
    ( r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_1333])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_938,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1646,plain,
    ( sK1 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_938])).

cnf(c_1716,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1445,c_1646])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_337,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_125])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | k2_relat_1(sK1) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_930,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_1009,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_930,c_7])).

cnf(c_62,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1028,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1009])).

cnf(c_1056,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1076,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1009,c_62,c_67,c_306,c_1028,c_1056])).

cnf(c_1352,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1349,c_1076])).

cnf(c_1365,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1352])).

cnf(c_66,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_68,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_1059,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1060,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_1195,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1202,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1339,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1340,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1401,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_68,c_307,c_1060,c_1076,c_1202,c_1324,c_1340,c_1357])).

cnf(c_1856,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1716,c_1401])).

cnf(c_1987,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1985,c_1856])).

cnf(c_1988,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK1) != X1
    | k1_relat_1(sK1) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_125])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_929,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1000,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_929,c_8])).

cnf(c_1057,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_1068,plain,
    ( k1_relat_1(sK1) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_307,c_1057])).

cnf(c_1069,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1068])).

cnf(c_1353,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1349,c_1069])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_64,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_65,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_550,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1110,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1112,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1370,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1353])).

cnf(c_1390,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1398,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_64,c_65,c_67,c_68,c_307,c_1060,c_1076,c_1112,c_1202,c_1324,c_1340,c_1370,c_1357,c_1390])).

cnf(c_1857,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1716,c_1398])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1988,c_1857])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.30/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.30/1.03  
% 2.30/1.03  ------  iProver source info
% 2.30/1.03  
% 2.30/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.30/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.30/1.03  git: non_committed_changes: false
% 2.30/1.03  git: last_make_outside_of_git: false
% 2.30/1.03  
% 2.30/1.03  ------ 
% 2.30/1.03  
% 2.30/1.03  ------ Input Options
% 2.30/1.03  
% 2.30/1.03  --out_options                           all
% 2.30/1.03  --tptp_safe_out                         true
% 2.30/1.03  --problem_path                          ""
% 2.30/1.03  --include_path                          ""
% 2.30/1.03  --clausifier                            res/vclausify_rel
% 2.30/1.03  --clausifier_options                    --mode clausify
% 2.30/1.03  --stdin                                 false
% 2.30/1.03  --stats_out                             all
% 2.30/1.03  
% 2.30/1.03  ------ General Options
% 2.30/1.03  
% 2.30/1.03  --fof                                   false
% 2.30/1.03  --time_out_real                         305.
% 2.30/1.03  --time_out_virtual                      -1.
% 2.30/1.03  --symbol_type_check                     false
% 2.30/1.03  --clausify_out                          false
% 2.30/1.03  --sig_cnt_out                           false
% 2.30/1.03  --trig_cnt_out                          false
% 2.30/1.03  --trig_cnt_out_tolerance                1.
% 2.30/1.03  --trig_cnt_out_sk_spl                   false
% 2.30/1.03  --abstr_cl_out                          false
% 2.30/1.03  
% 2.30/1.03  ------ Global Options
% 2.30/1.03  
% 2.30/1.03  --schedule                              default
% 2.30/1.03  --add_important_lit                     false
% 2.30/1.03  --prop_solver_per_cl                    1000
% 2.30/1.03  --min_unsat_core                        false
% 2.30/1.03  --soft_assumptions                      false
% 2.30/1.03  --soft_lemma_size                       3
% 2.30/1.03  --prop_impl_unit_size                   0
% 2.30/1.03  --prop_impl_unit                        []
% 2.30/1.03  --share_sel_clauses                     true
% 2.30/1.03  --reset_solvers                         false
% 2.30/1.03  --bc_imp_inh                            [conj_cone]
% 2.30/1.03  --conj_cone_tolerance                   3.
% 2.30/1.03  --extra_neg_conj                        none
% 2.30/1.03  --large_theory_mode                     true
% 2.30/1.03  --prolific_symb_bound                   200
% 2.30/1.03  --lt_threshold                          2000
% 2.30/1.03  --clause_weak_htbl                      true
% 2.30/1.03  --gc_record_bc_elim                     false
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing Options
% 2.30/1.03  
% 2.30/1.03  --preprocessing_flag                    true
% 2.30/1.03  --time_out_prep_mult                    0.1
% 2.30/1.03  --splitting_mode                        input
% 2.30/1.03  --splitting_grd                         true
% 2.30/1.03  --splitting_cvd                         false
% 2.30/1.03  --splitting_cvd_svl                     false
% 2.30/1.03  --splitting_nvd                         32
% 2.30/1.03  --sub_typing                            true
% 2.30/1.03  --prep_gs_sim                           true
% 2.30/1.03  --prep_unflatten                        true
% 2.30/1.03  --prep_res_sim                          true
% 2.30/1.03  --prep_upred                            true
% 2.30/1.03  --prep_sem_filter                       exhaustive
% 2.30/1.03  --prep_sem_filter_out                   false
% 2.30/1.03  --pred_elim                             true
% 2.30/1.03  --res_sim_input                         true
% 2.30/1.03  --eq_ax_congr_red                       true
% 2.30/1.03  --pure_diseq_elim                       true
% 2.30/1.03  --brand_transform                       false
% 2.30/1.03  --non_eq_to_eq                          false
% 2.30/1.03  --prep_def_merge                        true
% 2.30/1.03  --prep_def_merge_prop_impl              false
% 2.30/1.03  --prep_def_merge_mbd                    true
% 2.30/1.03  --prep_def_merge_tr_red                 false
% 2.30/1.03  --prep_def_merge_tr_cl                  false
% 2.30/1.03  --smt_preprocessing                     true
% 2.30/1.03  --smt_ac_axioms                         fast
% 2.30/1.03  --preprocessed_out                      false
% 2.30/1.03  --preprocessed_stats                    false
% 2.30/1.03  
% 2.30/1.03  ------ Abstraction refinement Options
% 2.30/1.03  
% 2.30/1.03  --abstr_ref                             []
% 2.30/1.03  --abstr_ref_prep                        false
% 2.30/1.03  --abstr_ref_until_sat                   false
% 2.30/1.03  --abstr_ref_sig_restrict                funpre
% 2.30/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/1.03  --abstr_ref_under                       []
% 2.30/1.03  
% 2.30/1.03  ------ SAT Options
% 2.30/1.03  
% 2.30/1.03  --sat_mode                              false
% 2.30/1.03  --sat_fm_restart_options                ""
% 2.30/1.03  --sat_gr_def                            false
% 2.30/1.03  --sat_epr_types                         true
% 2.30/1.03  --sat_non_cyclic_types                  false
% 2.30/1.03  --sat_finite_models                     false
% 2.30/1.03  --sat_fm_lemmas                         false
% 2.30/1.03  --sat_fm_prep                           false
% 2.30/1.03  --sat_fm_uc_incr                        true
% 2.30/1.03  --sat_out_model                         small
% 2.30/1.03  --sat_out_clauses                       false
% 2.30/1.03  
% 2.30/1.03  ------ QBF Options
% 2.30/1.03  
% 2.30/1.03  --qbf_mode                              false
% 2.30/1.03  --qbf_elim_univ                         false
% 2.30/1.03  --qbf_dom_inst                          none
% 2.30/1.03  --qbf_dom_pre_inst                      false
% 2.30/1.03  --qbf_sk_in                             false
% 2.30/1.03  --qbf_pred_elim                         true
% 2.30/1.03  --qbf_split                             512
% 2.30/1.03  
% 2.30/1.03  ------ BMC1 Options
% 2.30/1.03  
% 2.30/1.03  --bmc1_incremental                      false
% 2.30/1.03  --bmc1_axioms                           reachable_all
% 2.30/1.03  --bmc1_min_bound                        0
% 2.30/1.03  --bmc1_max_bound                        -1
% 2.30/1.03  --bmc1_max_bound_default                -1
% 2.30/1.03  --bmc1_symbol_reachability              true
% 2.30/1.03  --bmc1_property_lemmas                  false
% 2.30/1.03  --bmc1_k_induction                      false
% 2.30/1.03  --bmc1_non_equiv_states                 false
% 2.30/1.03  --bmc1_deadlock                         false
% 2.30/1.03  --bmc1_ucm                              false
% 2.30/1.03  --bmc1_add_unsat_core                   none
% 2.30/1.03  --bmc1_unsat_core_children              false
% 2.30/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/1.03  --bmc1_out_stat                         full
% 2.30/1.03  --bmc1_ground_init                      false
% 2.30/1.03  --bmc1_pre_inst_next_state              false
% 2.30/1.03  --bmc1_pre_inst_state                   false
% 2.30/1.03  --bmc1_pre_inst_reach_state             false
% 2.30/1.03  --bmc1_out_unsat_core                   false
% 2.30/1.03  --bmc1_aig_witness_out                  false
% 2.30/1.03  --bmc1_verbose                          false
% 2.30/1.03  --bmc1_dump_clauses_tptp                false
% 2.30/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.30/1.03  --bmc1_dump_file                        -
% 2.30/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.30/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.30/1.03  --bmc1_ucm_extend_mode                  1
% 2.30/1.03  --bmc1_ucm_init_mode                    2
% 2.30/1.03  --bmc1_ucm_cone_mode                    none
% 2.30/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.30/1.03  --bmc1_ucm_relax_model                  4
% 2.30/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.30/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/1.03  --bmc1_ucm_layered_model                none
% 2.30/1.03  --bmc1_ucm_max_lemma_size               10
% 2.30/1.03  
% 2.30/1.03  ------ AIG Options
% 2.30/1.03  
% 2.30/1.03  --aig_mode                              false
% 2.30/1.03  
% 2.30/1.03  ------ Instantiation Options
% 2.30/1.03  
% 2.30/1.03  --instantiation_flag                    true
% 2.30/1.03  --inst_sos_flag                         false
% 2.30/1.03  --inst_sos_phase                        true
% 2.30/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel_side                     num_symb
% 2.30/1.03  --inst_solver_per_active                1400
% 2.30/1.03  --inst_solver_calls_frac                1.
% 2.30/1.03  --inst_passive_queue_type               priority_queues
% 2.30/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.30/1.03  --inst_passive_queues_freq              [25;2]
% 2.30/1.03  --inst_dismatching                      true
% 2.30/1.03  --inst_eager_unprocessed_to_passive     true
% 2.30/1.03  --inst_prop_sim_given                   true
% 2.30/1.03  --inst_prop_sim_new                     false
% 2.30/1.03  --inst_subs_new                         false
% 2.30/1.03  --inst_eq_res_simp                      false
% 2.30/1.03  --inst_subs_given                       false
% 2.30/1.03  --inst_orphan_elimination               true
% 2.30/1.03  --inst_learning_loop_flag               true
% 2.30/1.03  --inst_learning_start                   3000
% 2.30/1.03  --inst_learning_factor                  2
% 2.30/1.03  --inst_start_prop_sim_after_learn       3
% 2.30/1.03  --inst_sel_renew                        solver
% 2.30/1.03  --inst_lit_activity_flag                true
% 2.30/1.03  --inst_restr_to_given                   false
% 2.30/1.03  --inst_activity_threshold               500
% 2.30/1.03  --inst_out_proof                        true
% 2.30/1.03  
% 2.30/1.03  ------ Resolution Options
% 2.30/1.03  
% 2.30/1.03  --resolution_flag                       true
% 2.30/1.03  --res_lit_sel                           adaptive
% 2.30/1.03  --res_lit_sel_side                      none
% 2.30/1.03  --res_ordering                          kbo
% 2.30/1.03  --res_to_prop_solver                    active
% 2.30/1.03  --res_prop_simpl_new                    false
% 2.30/1.03  --res_prop_simpl_given                  true
% 2.30/1.03  --res_passive_queue_type                priority_queues
% 2.30/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.30/1.03  --res_passive_queues_freq               [15;5]
% 2.30/1.03  --res_forward_subs                      full
% 2.30/1.03  --res_backward_subs                     full
% 2.30/1.03  --res_forward_subs_resolution           true
% 2.30/1.03  --res_backward_subs_resolution          true
% 2.30/1.03  --res_orphan_elimination                true
% 2.30/1.03  --res_time_limit                        2.
% 2.30/1.03  --res_out_proof                         true
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Options
% 2.30/1.03  
% 2.30/1.03  --superposition_flag                    true
% 2.30/1.03  --sup_passive_queue_type                priority_queues
% 2.30/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.30/1.03  --demod_completeness_check              fast
% 2.30/1.03  --demod_use_ground                      true
% 2.30/1.03  --sup_to_prop_solver                    passive
% 2.30/1.03  --sup_prop_simpl_new                    true
% 2.30/1.03  --sup_prop_simpl_given                  true
% 2.30/1.03  --sup_fun_splitting                     false
% 2.30/1.03  --sup_smt_interval                      50000
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Simplification Setup
% 2.30/1.03  
% 2.30/1.03  --sup_indices_passive                   []
% 2.30/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_full_bw                           [BwDemod]
% 2.30/1.03  --sup_immed_triv                        [TrivRules]
% 2.30/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_immed_bw_main                     []
% 2.30/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  
% 2.30/1.03  ------ Combination Options
% 2.30/1.03  
% 2.30/1.03  --comb_res_mult                         3
% 2.30/1.03  --comb_sup_mult                         2
% 2.30/1.03  --comb_inst_mult                        10
% 2.30/1.03  
% 2.30/1.03  ------ Debug Options
% 2.30/1.03  
% 2.30/1.03  --dbg_backtrace                         false
% 2.30/1.03  --dbg_dump_prop_clauses                 false
% 2.30/1.03  --dbg_dump_prop_clauses_file            -
% 2.30/1.03  --dbg_out_stat                          false
% 2.30/1.03  ------ Parsing...
% 2.30/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.30/1.03  ------ Proving...
% 2.30/1.03  ------ Problem Properties 
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  clauses                                 17
% 2.30/1.03  conjectures                             0
% 2.30/1.03  EPR                                     4
% 2.30/1.03  Horn                                    15
% 2.30/1.03  unary                                   4
% 2.30/1.03  binary                                  8
% 2.30/1.03  lits                                    38
% 2.30/1.03  lits eq                                 13
% 2.30/1.03  fd_pure                                 0
% 2.30/1.03  fd_pseudo                               0
% 2.30/1.03  fd_cond                                 1
% 2.30/1.03  fd_pseudo_cond                          1
% 2.30/1.03  AC symbols                              0
% 2.30/1.03  
% 2.30/1.03  ------ Schedule dynamic 5 is on 
% 2.30/1.03  
% 2.30/1.03  ------ no conjectures: strip conj schedule 
% 2.30/1.03  
% 2.30/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  ------ 
% 2.30/1.03  Current options:
% 2.30/1.03  ------ 
% 2.30/1.03  
% 2.30/1.03  ------ Input Options
% 2.30/1.03  
% 2.30/1.03  --out_options                           all
% 2.30/1.03  --tptp_safe_out                         true
% 2.30/1.03  --problem_path                          ""
% 2.30/1.03  --include_path                          ""
% 2.30/1.03  --clausifier                            res/vclausify_rel
% 2.30/1.03  --clausifier_options                    --mode clausify
% 2.30/1.03  --stdin                                 false
% 2.30/1.03  --stats_out                             all
% 2.30/1.03  
% 2.30/1.03  ------ General Options
% 2.30/1.03  
% 2.30/1.03  --fof                                   false
% 2.30/1.03  --time_out_real                         305.
% 2.30/1.03  --time_out_virtual                      -1.
% 2.30/1.03  --symbol_type_check                     false
% 2.30/1.03  --clausify_out                          false
% 2.30/1.03  --sig_cnt_out                           false
% 2.30/1.03  --trig_cnt_out                          false
% 2.30/1.03  --trig_cnt_out_tolerance                1.
% 2.30/1.03  --trig_cnt_out_sk_spl                   false
% 2.30/1.03  --abstr_cl_out                          false
% 2.30/1.03  
% 2.30/1.03  ------ Global Options
% 2.30/1.03  
% 2.30/1.03  --schedule                              default
% 2.30/1.03  --add_important_lit                     false
% 2.30/1.03  --prop_solver_per_cl                    1000
% 2.30/1.03  --min_unsat_core                        false
% 2.30/1.03  --soft_assumptions                      false
% 2.30/1.03  --soft_lemma_size                       3
% 2.30/1.03  --prop_impl_unit_size                   0
% 2.30/1.03  --prop_impl_unit                        []
% 2.30/1.03  --share_sel_clauses                     true
% 2.30/1.03  --reset_solvers                         false
% 2.30/1.03  --bc_imp_inh                            [conj_cone]
% 2.30/1.03  --conj_cone_tolerance                   3.
% 2.30/1.03  --extra_neg_conj                        none
% 2.30/1.03  --large_theory_mode                     true
% 2.30/1.03  --prolific_symb_bound                   200
% 2.30/1.03  --lt_threshold                          2000
% 2.30/1.03  --clause_weak_htbl                      true
% 2.30/1.03  --gc_record_bc_elim                     false
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing Options
% 2.30/1.03  
% 2.30/1.03  --preprocessing_flag                    true
% 2.30/1.03  --time_out_prep_mult                    0.1
% 2.30/1.03  --splitting_mode                        input
% 2.30/1.03  --splitting_grd                         true
% 2.30/1.03  --splitting_cvd                         false
% 2.30/1.03  --splitting_cvd_svl                     false
% 2.30/1.03  --splitting_nvd                         32
% 2.30/1.03  --sub_typing                            true
% 2.30/1.03  --prep_gs_sim                           true
% 2.30/1.03  --prep_unflatten                        true
% 2.30/1.03  --prep_res_sim                          true
% 2.30/1.03  --prep_upred                            true
% 2.30/1.03  --prep_sem_filter                       exhaustive
% 2.30/1.03  --prep_sem_filter_out                   false
% 2.30/1.03  --pred_elim                             true
% 2.30/1.03  --res_sim_input                         true
% 2.30/1.03  --eq_ax_congr_red                       true
% 2.30/1.03  --pure_diseq_elim                       true
% 2.30/1.03  --brand_transform                       false
% 2.30/1.03  --non_eq_to_eq                          false
% 2.30/1.03  --prep_def_merge                        true
% 2.30/1.03  --prep_def_merge_prop_impl              false
% 2.30/1.03  --prep_def_merge_mbd                    true
% 2.30/1.03  --prep_def_merge_tr_red                 false
% 2.30/1.03  --prep_def_merge_tr_cl                  false
% 2.30/1.03  --smt_preprocessing                     true
% 2.30/1.03  --smt_ac_axioms                         fast
% 2.30/1.03  --preprocessed_out                      false
% 2.30/1.03  --preprocessed_stats                    false
% 2.30/1.03  
% 2.30/1.03  ------ Abstraction refinement Options
% 2.30/1.03  
% 2.30/1.03  --abstr_ref                             []
% 2.30/1.03  --abstr_ref_prep                        false
% 2.30/1.03  --abstr_ref_until_sat                   false
% 2.30/1.03  --abstr_ref_sig_restrict                funpre
% 2.30/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/1.03  --abstr_ref_under                       []
% 2.30/1.03  
% 2.30/1.03  ------ SAT Options
% 2.30/1.03  
% 2.30/1.03  --sat_mode                              false
% 2.30/1.03  --sat_fm_restart_options                ""
% 2.30/1.03  --sat_gr_def                            false
% 2.30/1.03  --sat_epr_types                         true
% 2.30/1.03  --sat_non_cyclic_types                  false
% 2.30/1.03  --sat_finite_models                     false
% 2.30/1.03  --sat_fm_lemmas                         false
% 2.30/1.03  --sat_fm_prep                           false
% 2.30/1.03  --sat_fm_uc_incr                        true
% 2.30/1.03  --sat_out_model                         small
% 2.30/1.03  --sat_out_clauses                       false
% 2.30/1.03  
% 2.30/1.03  ------ QBF Options
% 2.30/1.03  
% 2.30/1.03  --qbf_mode                              false
% 2.30/1.03  --qbf_elim_univ                         false
% 2.30/1.03  --qbf_dom_inst                          none
% 2.30/1.03  --qbf_dom_pre_inst                      false
% 2.30/1.03  --qbf_sk_in                             false
% 2.30/1.03  --qbf_pred_elim                         true
% 2.30/1.03  --qbf_split                             512
% 2.30/1.03  
% 2.30/1.03  ------ BMC1 Options
% 2.30/1.03  
% 2.30/1.03  --bmc1_incremental                      false
% 2.30/1.03  --bmc1_axioms                           reachable_all
% 2.30/1.03  --bmc1_min_bound                        0
% 2.30/1.03  --bmc1_max_bound                        -1
% 2.30/1.03  --bmc1_max_bound_default                -1
% 2.30/1.03  --bmc1_symbol_reachability              true
% 2.30/1.03  --bmc1_property_lemmas                  false
% 2.30/1.03  --bmc1_k_induction                      false
% 2.30/1.03  --bmc1_non_equiv_states                 false
% 2.30/1.03  --bmc1_deadlock                         false
% 2.30/1.03  --bmc1_ucm                              false
% 2.30/1.03  --bmc1_add_unsat_core                   none
% 2.30/1.03  --bmc1_unsat_core_children              false
% 2.30/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/1.03  --bmc1_out_stat                         full
% 2.30/1.03  --bmc1_ground_init                      false
% 2.30/1.03  --bmc1_pre_inst_next_state              false
% 2.30/1.03  --bmc1_pre_inst_state                   false
% 2.30/1.03  --bmc1_pre_inst_reach_state             false
% 2.30/1.03  --bmc1_out_unsat_core                   false
% 2.30/1.03  --bmc1_aig_witness_out                  false
% 2.30/1.03  --bmc1_verbose                          false
% 2.30/1.03  --bmc1_dump_clauses_tptp                false
% 2.30/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.30/1.03  --bmc1_dump_file                        -
% 2.30/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.30/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.30/1.03  --bmc1_ucm_extend_mode                  1
% 2.30/1.03  --bmc1_ucm_init_mode                    2
% 2.30/1.03  --bmc1_ucm_cone_mode                    none
% 2.30/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.30/1.03  --bmc1_ucm_relax_model                  4
% 2.30/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.30/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/1.03  --bmc1_ucm_layered_model                none
% 2.30/1.03  --bmc1_ucm_max_lemma_size               10
% 2.30/1.03  
% 2.30/1.03  ------ AIG Options
% 2.30/1.03  
% 2.30/1.03  --aig_mode                              false
% 2.30/1.03  
% 2.30/1.03  ------ Instantiation Options
% 2.30/1.03  
% 2.30/1.03  --instantiation_flag                    true
% 2.30/1.03  --inst_sos_flag                         false
% 2.30/1.03  --inst_sos_phase                        true
% 2.30/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel_side                     none
% 2.30/1.03  --inst_solver_per_active                1400
% 2.30/1.03  --inst_solver_calls_frac                1.
% 2.30/1.03  --inst_passive_queue_type               priority_queues
% 2.30/1.03  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.30/1.03  --inst_passive_queues_freq              [25;2]
% 2.30/1.03  --inst_dismatching                      true
% 2.30/1.03  --inst_eager_unprocessed_to_passive     true
% 2.30/1.03  --inst_prop_sim_given                   true
% 2.30/1.03  --inst_prop_sim_new                     false
% 2.30/1.03  --inst_subs_new                         false
% 2.30/1.03  --inst_eq_res_simp                      false
% 2.30/1.03  --inst_subs_given                       false
% 2.30/1.03  --inst_orphan_elimination               true
% 2.30/1.03  --inst_learning_loop_flag               true
% 2.30/1.03  --inst_learning_start                   3000
% 2.30/1.03  --inst_learning_factor                  2
% 2.30/1.03  --inst_start_prop_sim_after_learn       3
% 2.30/1.03  --inst_sel_renew                        solver
% 2.30/1.03  --inst_lit_activity_flag                true
% 2.30/1.03  --inst_restr_to_given                   false
% 2.30/1.03  --inst_activity_threshold               500
% 2.30/1.03  --inst_out_proof                        true
% 2.30/1.03  
% 2.30/1.03  ------ Resolution Options
% 2.30/1.03  
% 2.30/1.03  --resolution_flag                       false
% 2.30/1.03  --res_lit_sel                           adaptive
% 2.30/1.03  --res_lit_sel_side                      none
% 2.30/1.03  --res_ordering                          kbo
% 2.30/1.03  --res_to_prop_solver                    active
% 2.30/1.03  --res_prop_simpl_new                    false
% 2.30/1.03  --res_prop_simpl_given                  true
% 2.30/1.03  --res_passive_queue_type                priority_queues
% 2.30/1.03  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.30/1.03  --res_passive_queues_freq               [15;5]
% 2.30/1.03  --res_forward_subs                      full
% 2.30/1.03  --res_backward_subs                     full
% 2.30/1.03  --res_forward_subs_resolution           true
% 2.30/1.03  --res_backward_subs_resolution          true
% 2.30/1.03  --res_orphan_elimination                true
% 2.30/1.03  --res_time_limit                        2.
% 2.30/1.03  --res_out_proof                         true
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Options
% 2.30/1.03  
% 2.30/1.03  --superposition_flag                    true
% 2.30/1.03  --sup_passive_queue_type                priority_queues
% 2.30/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.30/1.03  --demod_completeness_check              fast
% 2.30/1.03  --demod_use_ground                      true
% 2.30/1.03  --sup_to_prop_solver                    passive
% 2.30/1.03  --sup_prop_simpl_new                    true
% 2.30/1.03  --sup_prop_simpl_given                  true
% 2.30/1.03  --sup_fun_splitting                     false
% 2.30/1.03  --sup_smt_interval                      50000
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Simplification Setup
% 2.30/1.03  
% 2.30/1.03  --sup_indices_passive                   []
% 2.30/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_full_bw                           [BwDemod]
% 2.30/1.03  --sup_immed_triv                        [TrivRules]
% 2.30/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_immed_bw_main                     []
% 2.30/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  
% 2.30/1.03  ------ Combination Options
% 2.30/1.03  
% 2.30/1.03  --comb_res_mult                         3
% 2.30/1.03  --comb_sup_mult                         2
% 2.30/1.03  --comb_inst_mult                        10
% 2.30/1.03  
% 2.30/1.03  ------ Debug Options
% 2.30/1.03  
% 2.30/1.03  --dbg_backtrace                         false
% 2.30/1.03  --dbg_dump_prop_clauses                 false
% 2.30/1.03  --dbg_dump_prop_clauses_file            -
% 2.30/1.03  --dbg_out_stat                          false
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  ------ Proving...
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  % SZS status Theorem for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  fof(f3,axiom,(
% 2.30/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f26,plain,(
% 2.30/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/1.03    inference(nnf_transformation,[],[f3])).
% 2.30/1.03  
% 2.30/1.03  fof(f27,plain,(
% 2.30/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/1.03    inference(flattening,[],[f26])).
% 2.30/1.03  
% 2.30/1.03  fof(f39,plain,(
% 2.30/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.30/1.03    inference(cnf_transformation,[],[f27])).
% 2.30/1.03  
% 2.30/1.03  fof(f59,plain,(
% 2.30/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.30/1.03    inference(equality_resolution,[],[f39])).
% 2.30/1.03  
% 2.30/1.03  fof(f5,axiom,(
% 2.30/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f30,plain,(
% 2.30/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.30/1.03    inference(nnf_transformation,[],[f5])).
% 2.30/1.03  
% 2.30/1.03  fof(f45,plain,(
% 2.30/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f30])).
% 2.30/1.03  
% 2.30/1.03  fof(f4,axiom,(
% 2.30/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f28,plain,(
% 2.30/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.30/1.03    inference(nnf_transformation,[],[f4])).
% 2.30/1.03  
% 2.30/1.03  fof(f29,plain,(
% 2.30/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.30/1.03    inference(flattening,[],[f28])).
% 2.30/1.03  
% 2.30/1.03  fof(f43,plain,(
% 2.30/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.30/1.03    inference(cnf_transformation,[],[f29])).
% 2.30/1.03  
% 2.30/1.03  fof(f61,plain,(
% 2.30/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.30/1.03    inference(equality_resolution,[],[f43])).
% 2.30/1.03  
% 2.30/1.03  fof(f9,axiom,(
% 2.30/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f17,plain,(
% 2.30/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.30/1.03    inference(ennf_transformation,[],[f9])).
% 2.30/1.03  
% 2.30/1.03  fof(f49,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.30/1.03    inference(cnf_transformation,[],[f17])).
% 2.30/1.03  
% 2.30/1.03  fof(f1,axiom,(
% 2.30/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f13,plain,(
% 2.30/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.30/1.03    inference(ennf_transformation,[],[f1])).
% 2.30/1.03  
% 2.30/1.03  fof(f22,plain,(
% 2.30/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/1.03    inference(nnf_transformation,[],[f13])).
% 2.30/1.03  
% 2.30/1.03  fof(f23,plain,(
% 2.30/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/1.03    inference(rectify,[],[f22])).
% 2.30/1.03  
% 2.30/1.03  fof(f24,plain,(
% 2.30/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.30/1.03    introduced(choice_axiom,[])).
% 2.30/1.03  
% 2.30/1.03  fof(f25,plain,(
% 2.30/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.30/1.03  
% 2.30/1.03  fof(f35,plain,(
% 2.30/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f25])).
% 2.30/1.03  
% 2.30/1.03  fof(f2,axiom,(
% 2.30/1.03    v1_xboole_0(k1_xboole_0)),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f37,plain,(
% 2.30/1.03    v1_xboole_0(k1_xboole_0)),
% 2.30/1.03    inference(cnf_transformation,[],[f2])).
% 2.30/1.03  
% 2.30/1.03  fof(f6,axiom,(
% 2.30/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f14,plain,(
% 2.30/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.30/1.03    inference(ennf_transformation,[],[f6])).
% 2.30/1.03  
% 2.30/1.03  fof(f46,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f14])).
% 2.30/1.03  
% 2.30/1.03  fof(f10,axiom,(
% 2.30/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f18,plain,(
% 2.30/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.30/1.03    inference(ennf_transformation,[],[f10])).
% 2.30/1.03  
% 2.30/1.03  fof(f19,plain,(
% 2.30/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.30/1.03    inference(flattening,[],[f18])).
% 2.30/1.03  
% 2.30/1.03  fof(f31,plain,(
% 2.30/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.30/1.03    inference(nnf_transformation,[],[f19])).
% 2.30/1.03  
% 2.30/1.03  fof(f52,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.30/1.03    inference(cnf_transformation,[],[f31])).
% 2.30/1.03  
% 2.30/1.03  fof(f11,conjecture,(
% 2.30/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f12,negated_conjecture,(
% 2.30/1.03    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.30/1.03    inference(negated_conjecture,[],[f11])).
% 2.30/1.03  
% 2.30/1.03  fof(f20,plain,(
% 2.30/1.03    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.30/1.03    inference(ennf_transformation,[],[f12])).
% 2.30/1.03  
% 2.30/1.03  fof(f21,plain,(
% 2.30/1.03    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.30/1.03    inference(flattening,[],[f20])).
% 2.30/1.03  
% 2.30/1.03  fof(f32,plain,(
% 2.30/1.03    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.30/1.03    introduced(choice_axiom,[])).
% 2.30/1.03  
% 2.30/1.03  fof(f33,plain,(
% 2.30/1.03    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.30/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).
% 2.30/1.03  
% 2.30/1.03  fof(f58,plain,(
% 2.30/1.03    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 2.30/1.03    inference(cnf_transformation,[],[f33])).
% 2.30/1.03  
% 2.30/1.03  fof(f57,plain,(
% 2.30/1.03    v1_funct_1(sK1)),
% 2.30/1.03    inference(cnf_transformation,[],[f33])).
% 2.30/1.03  
% 2.30/1.03  fof(f7,axiom,(
% 2.30/1.03    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.30/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f15,plain,(
% 2.30/1.03    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.30/1.03    inference(ennf_transformation,[],[f7])).
% 2.30/1.03  
% 2.30/1.03  fof(f47,plain,(
% 2.30/1.03    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f15])).
% 2.30/1.03  
% 2.30/1.03  fof(f56,plain,(
% 2.30/1.03    v1_relat_1(sK1)),
% 2.30/1.03    inference(cnf_transformation,[],[f33])).
% 2.30/1.03  
% 2.30/1.03  fof(f40,plain,(
% 2.30/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f27])).
% 2.30/1.03  
% 2.30/1.03  fof(f55,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.30/1.03    inference(cnf_transformation,[],[f31])).
% 2.30/1.03  
% 2.30/1.03  fof(f63,plain,(
% 2.30/1.03    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.30/1.03    inference(equality_resolution,[],[f55])).
% 2.30/1.03  
% 2.30/1.03  fof(f64,plain,(
% 2.30/1.03    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.30/1.03    inference(equality_resolution,[],[f63])).
% 2.30/1.03  
% 2.30/1.03  fof(f38,plain,(
% 2.30/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.30/1.03    inference(cnf_transformation,[],[f27])).
% 2.30/1.03  
% 2.30/1.03  fof(f60,plain,(
% 2.30/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.30/1.03    inference(equality_resolution,[],[f38])).
% 2.30/1.03  
% 2.30/1.03  fof(f53,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.30/1.03    inference(cnf_transformation,[],[f31])).
% 2.30/1.03  
% 2.30/1.03  fof(f66,plain,(
% 2.30/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.30/1.03    inference(equality_resolution,[],[f53])).
% 2.30/1.03  
% 2.30/1.03  fof(f42,plain,(
% 2.30/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.30/1.03    inference(cnf_transformation,[],[f29])).
% 2.30/1.03  
% 2.30/1.03  fof(f62,plain,(
% 2.30/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.30/1.03    inference(equality_resolution,[],[f42])).
% 2.30/1.03  
% 2.30/1.03  fof(f41,plain,(
% 2.30/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f29])).
% 2.30/1.03  
% 2.30/1.03  cnf(c_5,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_937,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_10,plain,
% 2.30/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_936,plain,
% 2.30/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.30/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_7,plain,
% 2.30/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_15,plain,
% 2.30/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.30/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_933,plain,
% 2.30/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.30/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1581,plain,
% 2.30/1.03      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 2.30/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_7,c_933]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1605,plain,
% 2.30/1.03      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 2.30/1.03      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_936,c_1581]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1985,plain,
% 2.30/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_937,c_1605]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1,plain,
% 2.30/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_940,plain,
% 2.30/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.30/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_3,plain,
% 2.30/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_12,plain,
% 2.30/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.30/1.03      | ~ r2_hidden(X2,X0)
% 2.30/1.03      | ~ v1_xboole_0(X1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_178,plain,
% 2.30/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.30/1.03      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_179,plain,
% 2.30/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.30/1.03      inference(renaming,[status(thm)],[c_178]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_225,plain,
% 2.30/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.30/1.03      inference(bin_hyper_res,[status(thm)],[c_12,c_179]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_314,plain,
% 2.30/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.30/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_225]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_315,plain,
% 2.30/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.30/1.03      inference(unflattening,[status(thm)],[c_314]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_931,plain,
% 2.30/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.30/1.03      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1333,plain,
% 2.30/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.30/1.03      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_940,c_931]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1445,plain,
% 2.30/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_937,c_1333]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_19,plain,
% 2.30/1.03      ( v1_funct_2(X0,X1,X2)
% 2.30/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.30/1.03      | k1_relset_1(X1,X2,X0) != X1
% 2.30/1.03      | k1_xboole_0 = X2 ),
% 2.30/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_22,negated_conjecture,
% 2.30/1.03      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 2.30/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ v1_funct_1(sK1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_23,negated_conjecture,
% 2.30/1.03      ( v1_funct_1(sK1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_124,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_22,c_23]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_125,negated_conjecture,
% 2.30/1.03      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 2.30/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
% 2.30/1.03      inference(renaming,[status(thm)],[c_124]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_380,plain,
% 2.30/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.30/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | k1_relset_1(X1,X2,X0) != X1
% 2.30/1.03      | k2_relat_1(sK1) != X2
% 2.30/1.03      | k1_relat_1(sK1) != X1
% 2.30/1.03      | sK1 != X0
% 2.30/1.03      | k1_xboole_0 = X2 ),
% 2.30/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_125]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_381,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
% 2.30/1.03      | k1_xboole_0 = k2_relat_1(sK1) ),
% 2.30/1.03      inference(unflattening,[status(thm)],[c_380]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_389,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | k1_xboole_0 = k2_relat_1(sK1) ),
% 2.30/1.03      inference(forward_subsumption_resolution,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_381,c_15]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_928,plain,
% 2.30/1.03      ( k1_xboole_0 = k2_relat_1(sK1)
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1324,plain,
% 2.30/1.03      ( k2_relat_1(sK1) = k1_xboole_0
% 2.30/1.03      | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_936,c_928]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_13,plain,
% 2.30/1.03      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.30/1.03      | ~ v1_relat_1(X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_24,negated_conjecture,
% 2.30/1.03      ( v1_relat_1(sK1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_305,plain,
% 2.30/1.03      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.30/1.03      | sK1 != X0 ),
% 2.30/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_306,plain,
% 2.30/1.03      ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
% 2.30/1.03      inference(unflattening,[status(thm)],[c_305]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_307,plain,
% 2.30/1.03      ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1349,plain,
% 2.30/1.03      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_1324,c_307]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_932,plain,
% 2.30/1.03      ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1355,plain,
% 2.30/1.03      ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) = iProver_top ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1349,c_932]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1357,plain,
% 2.30/1.03      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1355,c_7]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1446,plain,
% 2.30/1.03      ( r1_tarski(sK1,X0) = iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_1357,c_1333]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_4,plain,
% 2.30/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_938,plain,
% 2.30/1.03      ( X0 = X1
% 2.30/1.03      | r1_tarski(X1,X0) != iProver_top
% 2.30/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1646,plain,
% 2.30/1.03      ( sK1 = X0 | r1_tarski(X0,sK1) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_1446,c_938]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1716,plain,
% 2.30/1.03      ( sK1 = k1_xboole_0 ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_1445,c_1646]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_16,plain,
% 2.30/1.03      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.30/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.30/1.03      | k1_xboole_0 = X0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_337,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.30/1.03      | k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != X0
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 = X0 ),
% 2.30/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_125]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_338,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
% 2.30/1.03      | k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 = k1_relat_1(sK1) ),
% 2.30/1.03      inference(unflattening,[status(thm)],[c_337]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_930,plain,
% 2.30/1.03      ( k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 = k1_relat_1(sK1)
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 2.30/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1009,plain,
% 2.30/1.03      ( k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) = k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 2.30/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_930,c_7]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_62,plain,
% 2.30/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.30/1.03      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_6,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_67,plain,
% 2.30/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1028,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.30/1.03      | k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) = k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0 ),
% 2.30/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1009]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1056,plain,
% 2.30/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1076,plain,
% 2.30/1.03      ( k2_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) = k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0 ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_1009,c_62,c_67,c_306,c_1028,c_1056]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1352,plain,
% 2.30/1.03      ( k1_relat_1(sK1) = k1_xboole_0
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1349,c_1076]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1365,plain,
% 2.30/1.03      ( k1_relat_1(sK1) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.30/1.03      inference(equality_resolution_simp,[status(thm)],[c_1352]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_66,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_68,plain,
% 2.30/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_66]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1059,plain,
% 2.30/1.03      ( ~ r1_tarski(sK1,k1_xboole_0)
% 2.30/1.03      | ~ r1_tarski(k1_xboole_0,sK1)
% 2.30/1.03      | sK1 = k1_xboole_0 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1060,plain,
% 2.30/1.03      ( sK1 = k1_xboole_0
% 2.30/1.03      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 2.30/1.03      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1059]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1195,plain,
% 2.30/1.03      ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
% 2.30/1.03      | r1_tarski(k1_xboole_0,sK1) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1202,plain,
% 2.30/1.03      ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) = iProver_top
% 2.30/1.03      | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1339,plain,
% 2.30/1.03      ( ~ r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
% 2.30/1.03      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_315]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1340,plain,
% 2.30/1.03      ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) != iProver_top
% 2.30/1.03      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1401,plain,
% 2.30/1.03      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_1365,c_68,c_307,c_1060,c_1076,c_1202,c_1324,c_1340,
% 2.30/1.03                 c_1357]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1856,plain,
% 2.30/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1716,c_1401]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1987,plain,
% 2.30/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.30/1.03      inference(light_normalisation,[status(thm)],[c_1985,c_1856]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1988,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_1987]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_18,plain,
% 2.30/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.30/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.30/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_364,plain,
% 2.30/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.30/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.30/1.03      | k2_relat_1(sK1) != X1
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | sK1 != X0 ),
% 2.30/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_125]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_365,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 2.30/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
% 2.30/1.03      | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0 ),
% 2.30/1.03      inference(unflattening,[status(thm)],[c_364]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_929,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_8,plain,
% 2.30/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1000,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_929,c_8]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1057,plain,
% 2.30/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) = iProver_top
% 2.30/1.03      | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1068,plain,
% 2.30/1.03      ( k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_1000,c_307,c_1057]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1069,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(renaming,[status(thm)],[c_1068]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1353,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0
% 2.30/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1349,c_1069]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_9,plain,
% 2.30/1.03      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 = X1
% 2.30/1.03      | k1_xboole_0 = X0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_64,plain,
% 2.30/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_65,plain,
% 2.30/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_550,plain,
% 2.30/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.30/1.03      theory(equality) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1110,plain,
% 2.30/1.03      ( ~ r1_tarski(X0,X1)
% 2.30/1.03      | r1_tarski(sK1,k1_xboole_0)
% 2.30/1.03      | sK1 != X0
% 2.30/1.03      | k1_xboole_0 != X1 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_550]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1112,plain,
% 2.30/1.03      ( r1_tarski(sK1,k1_xboole_0)
% 2.30/1.03      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.30/1.03      | sK1 != k1_xboole_0
% 2.30/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1370,plain,
% 2.30/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 2.30/1.03      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 2.30/1.03      | k1_relat_1(sK1) != k1_xboole_0 ),
% 2.30/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1353]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1390,plain,
% 2.30/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 2.30/1.03      | ~ r1_tarski(sK1,k1_xboole_0) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1398,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0 ),
% 2.30/1.03      inference(global_propositional_subsumption,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_1353,c_64,c_65,c_67,c_68,c_307,c_1060,c_1076,c_1112,
% 2.30/1.03                 c_1202,c_1324,c_1340,c_1370,c_1357,c_1390]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1857,plain,
% 2.30/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_1716,c_1398]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(contradiction,plain,
% 2.30/1.03      ( $false ),
% 2.30/1.03      inference(minisat,[status(thm)],[c_1988,c_1857]) ).
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  ------                               Statistics
% 2.30/1.03  
% 2.30/1.03  ------ General
% 2.30/1.03  
% 2.30/1.03  abstr_ref_over_cycles:                  0
% 2.30/1.03  abstr_ref_under_cycles:                 0
% 2.30/1.03  gc_basic_clause_elim:                   0
% 2.30/1.03  forced_gc_time:                         0
% 2.30/1.03  parsing_time:                           0.006
% 2.30/1.03  unif_index_cands_time:                  0.
% 2.30/1.03  unif_index_add_time:                    0.
% 2.30/1.03  orderings_time:                         0.
% 2.30/1.03  out_proof_time:                         0.015
% 2.30/1.03  total_time:                             0.07
% 2.30/1.03  num_of_symbols:                         46
% 2.30/1.03  num_of_terms:                           1727
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing
% 2.30/1.03  
% 2.30/1.03  num_of_splits:                          0
% 2.30/1.03  num_of_split_atoms:                     0
% 2.30/1.03  num_of_reused_defs:                     0
% 2.30/1.03  num_eq_ax_congr_red:                    12
% 2.30/1.03  num_of_sem_filtered_clauses:            2
% 2.30/1.03  num_of_subtypes:                        0
% 2.30/1.03  monotx_restored_types:                  0
% 2.30/1.03  sat_num_of_epr_types:                   0
% 2.30/1.03  sat_num_of_non_cyclic_types:            0
% 2.30/1.03  sat_guarded_non_collapsed_types:        0
% 2.30/1.03  num_pure_diseq_elim:                    0
% 2.30/1.03  simp_replaced_by:                       0
% 2.30/1.03  res_preprocessed:                       96
% 2.30/1.03  prep_upred:                             0
% 2.30/1.03  prep_unflattend:                        28
% 2.30/1.03  smt_new_axioms:                         0
% 2.30/1.03  pred_elim_cands:                        3
% 2.30/1.03  pred_elim:                              3
% 2.30/1.03  pred_elim_cl:                           6
% 2.30/1.03  pred_elim_cycles:                       5
% 2.30/1.03  merged_defs:                            8
% 2.30/1.03  merged_defs_ncl:                        0
% 2.30/1.03  bin_hyper_res:                          9
% 2.30/1.03  prep_cycles:                            4
% 2.30/1.03  pred_elim_time:                         0.002
% 2.30/1.03  splitting_time:                         0.
% 2.30/1.03  sem_filter_time:                        0.
% 2.30/1.03  monotx_time:                            0.
% 2.30/1.03  subtype_inf_time:                       0.
% 2.30/1.03  
% 2.30/1.03  ------ Problem properties
% 2.30/1.03  
% 2.30/1.03  clauses:                                17
% 2.30/1.03  conjectures:                            0
% 2.30/1.03  epr:                                    4
% 2.30/1.03  horn:                                   15
% 2.30/1.03  ground:                                 4
% 2.30/1.03  unary:                                  4
% 2.30/1.03  binary:                                 8
% 2.30/1.03  lits:                                   38
% 2.30/1.03  lits_eq:                                13
% 2.30/1.03  fd_pure:                                0
% 2.30/1.03  fd_pseudo:                              0
% 2.30/1.03  fd_cond:                                1
% 2.30/1.03  fd_pseudo_cond:                         1
% 2.30/1.03  ac_symbols:                             0
% 2.30/1.03  
% 2.30/1.03  ------ Propositional Solver
% 2.30/1.03  
% 2.30/1.03  prop_solver_calls:                      26
% 2.30/1.03  prop_fast_solver_calls:                 541
% 2.30/1.03  smt_solver_calls:                       0
% 2.30/1.03  smt_fast_solver_calls:                  0
% 2.30/1.03  prop_num_of_clauses:                    589
% 2.30/1.03  prop_preprocess_simplified:             3128
% 2.30/1.03  prop_fo_subsumed:                       8
% 2.30/1.03  prop_solver_time:                       0.
% 2.30/1.03  smt_solver_time:                        0.
% 2.30/1.03  smt_fast_solver_time:                   0.
% 2.30/1.03  prop_fast_solver_time:                  0.
% 2.30/1.03  prop_unsat_core_time:                   0.
% 2.30/1.03  
% 2.30/1.03  ------ QBF
% 2.30/1.03  
% 2.30/1.03  qbf_q_res:                              0
% 2.30/1.03  qbf_num_tautologies:                    0
% 2.30/1.03  qbf_prep_cycles:                        0
% 2.30/1.03  
% 2.30/1.03  ------ BMC1
% 2.30/1.03  
% 2.30/1.03  bmc1_current_bound:                     -1
% 2.30/1.03  bmc1_last_solved_bound:                 -1
% 2.30/1.03  bmc1_unsat_core_size:                   -1
% 2.30/1.03  bmc1_unsat_core_parents_size:           -1
% 2.30/1.03  bmc1_merge_next_fun:                    0
% 2.30/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.30/1.03  
% 2.30/1.03  ------ Instantiation
% 2.30/1.03  
% 2.30/1.03  inst_num_of_clauses:                    185
% 2.30/1.03  inst_num_in_passive:                    60
% 2.30/1.03  inst_num_in_active:                     125
% 2.30/1.03  inst_num_in_unprocessed:                0
% 2.30/1.03  inst_num_of_loops:                      160
% 2.30/1.03  inst_num_of_learning_restarts:          0
% 2.30/1.03  inst_num_moves_active_passive:          32
% 2.30/1.03  inst_lit_activity:                      0
% 2.30/1.03  inst_lit_activity_moves:                0
% 2.30/1.03  inst_num_tautologies:                   0
% 2.30/1.03  inst_num_prop_implied:                  0
% 2.30/1.03  inst_num_existing_simplified:           0
% 2.30/1.03  inst_num_eq_res_simplified:             0
% 2.30/1.03  inst_num_child_elim:                    0
% 2.30/1.03  inst_num_of_dismatching_blockings:      33
% 2.30/1.03  inst_num_of_non_proper_insts:           132
% 2.30/1.03  inst_num_of_duplicates:                 0
% 2.30/1.03  inst_inst_num_from_inst_to_res:         0
% 2.30/1.03  inst_dismatching_checking_time:         0.
% 2.30/1.03  
% 2.30/1.03  ------ Resolution
% 2.30/1.03  
% 2.30/1.03  res_num_of_clauses:                     0
% 2.30/1.03  res_num_in_passive:                     0
% 2.30/1.03  res_num_in_active:                      0
% 2.30/1.03  res_num_of_loops:                       100
% 2.30/1.03  res_forward_subset_subsumed:            10
% 2.30/1.03  res_backward_subset_subsumed:           0
% 2.30/1.03  res_forward_subsumed:                   0
% 2.30/1.03  res_backward_subsumed:                  0
% 2.30/1.03  res_forward_subsumption_resolution:     1
% 2.30/1.03  res_backward_subsumption_resolution:    0
% 2.30/1.03  res_clause_to_clause_subsumption:       122
% 2.30/1.03  res_orphan_elimination:                 0
% 2.30/1.03  res_tautology_del:                      31
% 2.30/1.03  res_num_eq_res_simplified:              0
% 2.30/1.03  res_num_sel_changes:                    0
% 2.30/1.03  res_moves_from_active_to_pass:          0
% 2.30/1.03  
% 2.30/1.03  ------ Superposition
% 2.30/1.03  
% 2.30/1.03  sup_time_total:                         0.
% 2.30/1.03  sup_time_generating:                    0.
% 2.30/1.03  sup_time_sim_full:                      0.
% 2.30/1.03  sup_time_sim_immed:                     0.
% 2.30/1.03  
% 2.30/1.03  sup_num_of_clauses:                     32
% 2.30/1.03  sup_num_in_active:                      22
% 2.30/1.03  sup_num_in_passive:                     10
% 2.30/1.03  sup_num_of_loops:                       31
% 2.30/1.03  sup_fw_superposition:                   21
% 2.30/1.03  sup_bw_superposition:                   9
% 2.30/1.03  sup_immediate_simplified:               6
% 2.30/1.03  sup_given_eliminated:                   1
% 2.30/1.03  comparisons_done:                       0
% 2.30/1.03  comparisons_avoided:                    0
% 2.30/1.03  
% 2.30/1.03  ------ Simplifications
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  sim_fw_subset_subsumed:                 0
% 2.30/1.03  sim_bw_subset_subsumed:                 0
% 2.30/1.03  sim_fw_subsumed:                        2
% 2.30/1.03  sim_bw_subsumed:                        0
% 2.30/1.03  sim_fw_subsumption_res:                 0
% 2.30/1.03  sim_bw_subsumption_res:                 0
% 2.30/1.03  sim_tautology_del:                      1
% 2.30/1.03  sim_eq_tautology_del:                   5
% 2.30/1.03  sim_eq_res_simp:                        1
% 2.30/1.03  sim_fw_demodulated:                     5
% 2.30/1.03  sim_bw_demodulated:                     10
% 2.30/1.03  sim_light_normalised:                   1
% 2.30/1.03  sim_joinable_taut:                      0
% 2.30/1.03  sim_joinable_simp:                      0
% 2.30/1.03  sim_ac_normalised:                      0
% 2.30/1.03  sim_smt_subsumption:                    0
% 2.30/1.03  
%------------------------------------------------------------------------------
