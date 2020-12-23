%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:09 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 686 expanded)
%              Number of clauses        :   72 ( 207 expanded)
%              Number of leaves         :   14 ( 170 expanded)
%              Depth                    :   24
%              Number of atoms          :  425 (4520 expanded)
%              Number of equality atoms :  202 (1057 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ! [X4] :
        ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
        | ~ r2_hidden(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f48,f47])).

fof(f79,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1097,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_451,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_453,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_27])).

cnf(c_1085,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1087,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2046,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1085,c_1087])).

cnf(c_2195,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_2046])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_462,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_464,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_30])).

cnf(c_1083,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2047,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1083,c_1087])).

cnf(c_2198,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_464,c_2047])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1090,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3138,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1090])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1334,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_3413,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_36,c_38,c_1334])).

cnf(c_3414,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3413])).

cnf(c_3426,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_3414])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1337,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_3439,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3426,c_33,c_35,c_1337])).

cnf(c_3446,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_3439])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1086,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3495,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3446,c_1086])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1091,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3721,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1091])).

cnf(c_3738,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3721])).

cnf(c_4292,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3721,c_33,c_35,c_36,c_38,c_1334,c_1337])).

cnf(c_4297,plain,
    ( k1_relat_1(sK4) != sK2
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2195,c_4292])).

cnf(c_4537,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_2198])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_27])).

cnf(c_1081,plain,
    ( sK4 != sK5
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_4553,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4537,c_1081])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_342,plain,
    ( sK4 != sK5
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1306,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_658,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1584,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1586,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1088,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2567,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1088])).

cnf(c_2592,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2567])).

cnf(c_2568,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_1088])).

cnf(c_2593,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2568])).

cnf(c_4576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4553,c_0,c_342,c_1306,c_1586,c_2592,c_2593])).

cnf(c_4583,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1097,c_4576])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.66/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/0.99  
% 2.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/0.99  
% 2.66/0.99  ------  iProver source info
% 2.66/0.99  
% 2.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/0.99  git: non_committed_changes: false
% 2.66/0.99  git: last_make_outside_of_git: false
% 2.66/0.99  
% 2.66/0.99  ------ 
% 2.66/0.99  
% 2.66/0.99  ------ Input Options
% 2.66/0.99  
% 2.66/0.99  --out_options                           all
% 2.66/0.99  --tptp_safe_out                         true
% 2.66/0.99  --problem_path                          ""
% 2.66/0.99  --include_path                          ""
% 2.66/0.99  --clausifier                            res/vclausify_rel
% 2.66/0.99  --clausifier_options                    --mode clausify
% 2.66/0.99  --stdin                                 false
% 2.66/0.99  --stats_out                             all
% 2.66/0.99  
% 2.66/0.99  ------ General Options
% 2.66/0.99  
% 2.66/0.99  --fof                                   false
% 2.66/0.99  --time_out_real                         305.
% 2.66/0.99  --time_out_virtual                      -1.
% 2.66/0.99  --symbol_type_check                     false
% 2.66/0.99  --clausify_out                          false
% 2.66/0.99  --sig_cnt_out                           false
% 2.66/0.99  --trig_cnt_out                          false
% 2.66/0.99  --trig_cnt_out_tolerance                1.
% 2.66/0.99  --trig_cnt_out_sk_spl                   false
% 2.66/0.99  --abstr_cl_out                          false
% 2.66/0.99  
% 2.66/0.99  ------ Global Options
% 2.66/0.99  
% 2.66/0.99  --schedule                              default
% 2.66/0.99  --add_important_lit                     false
% 2.66/0.99  --prop_solver_per_cl                    1000
% 2.66/0.99  --min_unsat_core                        false
% 2.66/0.99  --soft_assumptions                      false
% 2.66/0.99  --soft_lemma_size                       3
% 2.66/0.99  --prop_impl_unit_size                   0
% 2.66/0.99  --prop_impl_unit                        []
% 2.66/0.99  --share_sel_clauses                     true
% 2.66/0.99  --reset_solvers                         false
% 2.66/0.99  --bc_imp_inh                            [conj_cone]
% 2.66/0.99  --conj_cone_tolerance                   3.
% 2.66/0.99  --extra_neg_conj                        none
% 2.66/0.99  --large_theory_mode                     true
% 2.66/0.99  --prolific_symb_bound                   200
% 2.66/0.99  --lt_threshold                          2000
% 2.66/0.99  --clause_weak_htbl                      true
% 2.66/0.99  --gc_record_bc_elim                     false
% 2.66/0.99  
% 2.66/0.99  ------ Preprocessing Options
% 2.66/0.99  
% 2.66/0.99  --preprocessing_flag                    true
% 2.66/0.99  --time_out_prep_mult                    0.1
% 2.66/0.99  --splitting_mode                        input
% 2.66/0.99  --splitting_grd                         true
% 2.66/0.99  --splitting_cvd                         false
% 2.66/0.99  --splitting_cvd_svl                     false
% 2.66/0.99  --splitting_nvd                         32
% 2.66/0.99  --sub_typing                            true
% 2.66/0.99  --prep_gs_sim                           true
% 2.66/0.99  --prep_unflatten                        true
% 2.66/0.99  --prep_res_sim                          true
% 2.66/0.99  --prep_upred                            true
% 2.66/0.99  --prep_sem_filter                       exhaustive
% 2.66/0.99  --prep_sem_filter_out                   false
% 2.66/0.99  --pred_elim                             true
% 2.66/0.99  --res_sim_input                         true
% 2.66/0.99  --eq_ax_congr_red                       true
% 2.66/0.99  --pure_diseq_elim                       true
% 2.66/0.99  --brand_transform                       false
% 2.66/0.99  --non_eq_to_eq                          false
% 2.66/0.99  --prep_def_merge                        true
% 2.66/0.99  --prep_def_merge_prop_impl              false
% 2.66/0.99  --prep_def_merge_mbd                    true
% 2.66/0.99  --prep_def_merge_tr_red                 false
% 2.66/0.99  --prep_def_merge_tr_cl                  false
% 2.66/0.99  --smt_preprocessing                     true
% 2.66/0.99  --smt_ac_axioms                         fast
% 2.66/0.99  --preprocessed_out                      false
% 2.66/0.99  --preprocessed_stats                    false
% 2.66/0.99  
% 2.66/0.99  ------ Abstraction refinement Options
% 2.66/0.99  
% 2.66/0.99  --abstr_ref                             []
% 2.66/0.99  --abstr_ref_prep                        false
% 2.66/0.99  --abstr_ref_until_sat                   false
% 2.66/0.99  --abstr_ref_sig_restrict                funpre
% 2.66/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.99  --abstr_ref_under                       []
% 2.66/0.99  
% 2.66/0.99  ------ SAT Options
% 2.66/0.99  
% 2.66/0.99  --sat_mode                              false
% 2.66/0.99  --sat_fm_restart_options                ""
% 2.66/0.99  --sat_gr_def                            false
% 2.66/0.99  --sat_epr_types                         true
% 2.66/0.99  --sat_non_cyclic_types                  false
% 2.66/0.99  --sat_finite_models                     false
% 2.66/0.99  --sat_fm_lemmas                         false
% 2.66/0.99  --sat_fm_prep                           false
% 2.66/0.99  --sat_fm_uc_incr                        true
% 2.66/0.99  --sat_out_model                         small
% 2.66/0.99  --sat_out_clauses                       false
% 2.66/0.99  
% 2.66/0.99  ------ QBF Options
% 2.66/0.99  
% 2.66/0.99  --qbf_mode                              false
% 2.66/0.99  --qbf_elim_univ                         false
% 2.66/0.99  --qbf_dom_inst                          none
% 2.66/0.99  --qbf_dom_pre_inst                      false
% 2.66/0.99  --qbf_sk_in                             false
% 2.66/0.99  --qbf_pred_elim                         true
% 2.66/0.99  --qbf_split                             512
% 2.66/0.99  
% 2.66/0.99  ------ BMC1 Options
% 2.66/0.99  
% 2.66/0.99  --bmc1_incremental                      false
% 2.66/0.99  --bmc1_axioms                           reachable_all
% 2.66/0.99  --bmc1_min_bound                        0
% 2.66/0.99  --bmc1_max_bound                        -1
% 2.66/0.99  --bmc1_max_bound_default                -1
% 2.66/0.99  --bmc1_symbol_reachability              true
% 2.66/0.99  --bmc1_property_lemmas                  false
% 2.66/0.99  --bmc1_k_induction                      false
% 2.66/0.99  --bmc1_non_equiv_states                 false
% 2.66/0.99  --bmc1_deadlock                         false
% 2.66/0.99  --bmc1_ucm                              false
% 2.66/0.99  --bmc1_add_unsat_core                   none
% 2.66/0.99  --bmc1_unsat_core_children              false
% 2.66/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.99  --bmc1_out_stat                         full
% 2.66/0.99  --bmc1_ground_init                      false
% 2.66/0.99  --bmc1_pre_inst_next_state              false
% 2.66/0.99  --bmc1_pre_inst_state                   false
% 2.66/0.99  --bmc1_pre_inst_reach_state             false
% 2.66/0.99  --bmc1_out_unsat_core                   false
% 2.66/0.99  --bmc1_aig_witness_out                  false
% 2.66/0.99  --bmc1_verbose                          false
% 2.66/0.99  --bmc1_dump_clauses_tptp                false
% 2.66/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.99  --bmc1_dump_file                        -
% 2.66/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.99  --bmc1_ucm_extend_mode                  1
% 2.66/0.99  --bmc1_ucm_init_mode                    2
% 2.66/0.99  --bmc1_ucm_cone_mode                    none
% 2.66/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.99  --bmc1_ucm_relax_model                  4
% 2.66/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.99  --bmc1_ucm_layered_model                none
% 2.66/0.99  --bmc1_ucm_max_lemma_size               10
% 2.66/0.99  
% 2.66/0.99  ------ AIG Options
% 2.66/0.99  
% 2.66/0.99  --aig_mode                              false
% 2.66/0.99  
% 2.66/0.99  ------ Instantiation Options
% 2.66/0.99  
% 2.66/0.99  --instantiation_flag                    true
% 2.66/0.99  --inst_sos_flag                         false
% 2.66/0.99  --inst_sos_phase                        true
% 2.66/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.99  --inst_lit_sel_side                     num_symb
% 2.66/0.99  --inst_solver_per_active                1400
% 2.66/0.99  --inst_solver_calls_frac                1.
% 2.66/0.99  --inst_passive_queue_type               priority_queues
% 2.66/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.99  --inst_passive_queues_freq              [25;2]
% 2.66/0.99  --inst_dismatching                      true
% 2.66/0.99  --inst_eager_unprocessed_to_passive     true
% 2.66/0.99  --inst_prop_sim_given                   true
% 2.66/0.99  --inst_prop_sim_new                     false
% 2.66/0.99  --inst_subs_new                         false
% 2.66/0.99  --inst_eq_res_simp                      false
% 2.66/0.99  --inst_subs_given                       false
% 2.66/0.99  --inst_orphan_elimination               true
% 2.66/0.99  --inst_learning_loop_flag               true
% 2.66/0.99  --inst_learning_start                   3000
% 2.66/0.99  --inst_learning_factor                  2
% 2.66/0.99  --inst_start_prop_sim_after_learn       3
% 2.66/0.99  --inst_sel_renew                        solver
% 2.66/0.99  --inst_lit_activity_flag                true
% 2.66/0.99  --inst_restr_to_given                   false
% 2.66/0.99  --inst_activity_threshold               500
% 2.66/0.99  --inst_out_proof                        true
% 2.66/0.99  
% 2.66/0.99  ------ Resolution Options
% 2.66/0.99  
% 2.66/0.99  --resolution_flag                       true
% 2.66/0.99  --res_lit_sel                           adaptive
% 2.66/0.99  --res_lit_sel_side                      none
% 2.66/0.99  --res_ordering                          kbo
% 2.66/0.99  --res_to_prop_solver                    active
% 2.66/0.99  --res_prop_simpl_new                    false
% 2.66/0.99  --res_prop_simpl_given                  true
% 2.66/0.99  --res_passive_queue_type                priority_queues
% 2.66/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.99  --res_passive_queues_freq               [15;5]
% 2.66/0.99  --res_forward_subs                      full
% 2.66/0.99  --res_backward_subs                     full
% 2.66/0.99  --res_forward_subs_resolution           true
% 2.66/0.99  --res_backward_subs_resolution          true
% 2.66/0.99  --res_orphan_elimination                true
% 2.66/0.99  --res_time_limit                        2.
% 2.66/0.99  --res_out_proof                         true
% 2.66/0.99  
% 2.66/0.99  ------ Superposition Options
% 2.66/0.99  
% 2.66/0.99  --superposition_flag                    true
% 2.66/0.99  --sup_passive_queue_type                priority_queues
% 2.66/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.99  --demod_completeness_check              fast
% 2.66/0.99  --demod_use_ground                      true
% 2.66/0.99  --sup_to_prop_solver                    passive
% 2.66/0.99  --sup_prop_simpl_new                    true
% 2.66/0.99  --sup_prop_simpl_given                  true
% 2.66/0.99  --sup_fun_splitting                     false
% 2.66/0.99  --sup_smt_interval                      50000
% 2.66/0.99  
% 2.66/0.99  ------ Superposition Simplification Setup
% 2.66/0.99  
% 2.66/0.99  --sup_indices_passive                   []
% 2.66/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_full_bw                           [BwDemod]
% 2.66/0.99  --sup_immed_triv                        [TrivRules]
% 2.66/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_immed_bw_main                     []
% 2.66/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.99  
% 2.66/0.99  ------ Combination Options
% 2.66/0.99  
% 2.66/0.99  --comb_res_mult                         3
% 2.66/0.99  --comb_sup_mult                         2
% 2.66/0.99  --comb_inst_mult                        10
% 2.66/0.99  
% 2.66/0.99  ------ Debug Options
% 2.66/0.99  
% 2.66/0.99  --dbg_backtrace                         false
% 2.66/0.99  --dbg_dump_prop_clauses                 false
% 2.66/0.99  --dbg_dump_prop_clauses_file            -
% 2.66/0.99  --dbg_out_stat                          false
% 2.66/0.99  ------ Parsing...
% 2.66/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/0.99  
% 2.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.66/0.99  
% 2.66/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/0.99  
% 2.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/0.99  ------ Proving...
% 2.66/0.99  ------ Problem Properties 
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  clauses                                 29
% 2.66/0.99  conjectures                             5
% 2.66/0.99  EPR                                     4
% 2.66/0.99  Horn                                    23
% 2.66/0.99  unary                                   9
% 2.66/0.99  binary                                  7
% 2.66/0.99  lits                                    73
% 2.66/0.99  lits eq                                 29
% 2.66/0.99  fd_pure                                 0
% 2.66/0.99  fd_pseudo                               0
% 2.66/0.99  fd_cond                                 1
% 2.66/0.99  fd_pseudo_cond                          3
% 2.66/0.99  AC symbols                              0
% 2.66/0.99  
% 2.66/0.99  ------ Schedule dynamic 5 is on 
% 2.66/0.99  
% 2.66/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  ------ 
% 2.66/0.99  Current options:
% 2.66/0.99  ------ 
% 2.66/0.99  
% 2.66/0.99  ------ Input Options
% 2.66/0.99  
% 2.66/0.99  --out_options                           all
% 2.66/0.99  --tptp_safe_out                         true
% 2.66/0.99  --problem_path                          ""
% 2.66/0.99  --include_path                          ""
% 2.66/0.99  --clausifier                            res/vclausify_rel
% 2.66/0.99  --clausifier_options                    --mode clausify
% 2.66/0.99  --stdin                                 false
% 2.66/0.99  --stats_out                             all
% 2.66/0.99  
% 2.66/0.99  ------ General Options
% 2.66/0.99  
% 2.66/0.99  --fof                                   false
% 2.66/0.99  --time_out_real                         305.
% 2.66/0.99  --time_out_virtual                      -1.
% 2.66/0.99  --symbol_type_check                     false
% 2.66/0.99  --clausify_out                          false
% 2.66/0.99  --sig_cnt_out                           false
% 2.66/0.99  --trig_cnt_out                          false
% 2.66/0.99  --trig_cnt_out_tolerance                1.
% 2.66/0.99  --trig_cnt_out_sk_spl                   false
% 2.66/0.99  --abstr_cl_out                          false
% 2.66/0.99  
% 2.66/0.99  ------ Global Options
% 2.66/0.99  
% 2.66/0.99  --schedule                              default
% 2.66/0.99  --add_important_lit                     false
% 2.66/0.99  --prop_solver_per_cl                    1000
% 2.66/0.99  --min_unsat_core                        false
% 2.66/0.99  --soft_assumptions                      false
% 2.66/0.99  --soft_lemma_size                       3
% 2.66/0.99  --prop_impl_unit_size                   0
% 2.66/0.99  --prop_impl_unit                        []
% 2.66/0.99  --share_sel_clauses                     true
% 2.66/0.99  --reset_solvers                         false
% 2.66/0.99  --bc_imp_inh                            [conj_cone]
% 2.66/0.99  --conj_cone_tolerance                   3.
% 2.66/0.99  --extra_neg_conj                        none
% 2.66/0.99  --large_theory_mode                     true
% 2.66/0.99  --prolific_symb_bound                   200
% 2.66/0.99  --lt_threshold                          2000
% 2.66/0.99  --clause_weak_htbl                      true
% 2.66/0.99  --gc_record_bc_elim                     false
% 2.66/0.99  
% 2.66/0.99  ------ Preprocessing Options
% 2.66/0.99  
% 2.66/0.99  --preprocessing_flag                    true
% 2.66/0.99  --time_out_prep_mult                    0.1
% 2.66/0.99  --splitting_mode                        input
% 2.66/0.99  --splitting_grd                         true
% 2.66/0.99  --splitting_cvd                         false
% 2.66/0.99  --splitting_cvd_svl                     false
% 2.66/0.99  --splitting_nvd                         32
% 2.66/0.99  --sub_typing                            true
% 2.66/0.99  --prep_gs_sim                           true
% 2.66/0.99  --prep_unflatten                        true
% 2.66/0.99  --prep_res_sim                          true
% 2.66/0.99  --prep_upred                            true
% 2.66/0.99  --prep_sem_filter                       exhaustive
% 2.66/0.99  --prep_sem_filter_out                   false
% 2.66/0.99  --pred_elim                             true
% 2.66/0.99  --res_sim_input                         true
% 2.66/0.99  --eq_ax_congr_red                       true
% 2.66/0.99  --pure_diseq_elim                       true
% 2.66/0.99  --brand_transform                       false
% 2.66/0.99  --non_eq_to_eq                          false
% 2.66/0.99  --prep_def_merge                        true
% 2.66/0.99  --prep_def_merge_prop_impl              false
% 2.66/0.99  --prep_def_merge_mbd                    true
% 2.66/0.99  --prep_def_merge_tr_red                 false
% 2.66/0.99  --prep_def_merge_tr_cl                  false
% 2.66/0.99  --smt_preprocessing                     true
% 2.66/0.99  --smt_ac_axioms                         fast
% 2.66/0.99  --preprocessed_out                      false
% 2.66/0.99  --preprocessed_stats                    false
% 2.66/0.99  
% 2.66/0.99  ------ Abstraction refinement Options
% 2.66/0.99  
% 2.66/0.99  --abstr_ref                             []
% 2.66/0.99  --abstr_ref_prep                        false
% 2.66/0.99  --abstr_ref_until_sat                   false
% 2.66/0.99  --abstr_ref_sig_restrict                funpre
% 2.66/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.99  --abstr_ref_under                       []
% 2.66/0.99  
% 2.66/0.99  ------ SAT Options
% 2.66/0.99  
% 2.66/0.99  --sat_mode                              false
% 2.66/0.99  --sat_fm_restart_options                ""
% 2.66/0.99  --sat_gr_def                            false
% 2.66/0.99  --sat_epr_types                         true
% 2.66/0.99  --sat_non_cyclic_types                  false
% 2.66/0.99  --sat_finite_models                     false
% 2.66/0.99  --sat_fm_lemmas                         false
% 2.66/0.99  --sat_fm_prep                           false
% 2.66/0.99  --sat_fm_uc_incr                        true
% 2.66/0.99  --sat_out_model                         small
% 2.66/0.99  --sat_out_clauses                       false
% 2.66/0.99  
% 2.66/0.99  ------ QBF Options
% 2.66/0.99  
% 2.66/0.99  --qbf_mode                              false
% 2.66/0.99  --qbf_elim_univ                         false
% 2.66/0.99  --qbf_dom_inst                          none
% 2.66/0.99  --qbf_dom_pre_inst                      false
% 2.66/0.99  --qbf_sk_in                             false
% 2.66/0.99  --qbf_pred_elim                         true
% 2.66/0.99  --qbf_split                             512
% 2.66/0.99  
% 2.66/0.99  ------ BMC1 Options
% 2.66/0.99  
% 2.66/0.99  --bmc1_incremental                      false
% 2.66/0.99  --bmc1_axioms                           reachable_all
% 2.66/0.99  --bmc1_min_bound                        0
% 2.66/0.99  --bmc1_max_bound                        -1
% 2.66/0.99  --bmc1_max_bound_default                -1
% 2.66/0.99  --bmc1_symbol_reachability              true
% 2.66/0.99  --bmc1_property_lemmas                  false
% 2.66/0.99  --bmc1_k_induction                      false
% 2.66/0.99  --bmc1_non_equiv_states                 false
% 2.66/0.99  --bmc1_deadlock                         false
% 2.66/0.99  --bmc1_ucm                              false
% 2.66/0.99  --bmc1_add_unsat_core                   none
% 2.66/0.99  --bmc1_unsat_core_children              false
% 2.66/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.99  --bmc1_out_stat                         full
% 2.66/0.99  --bmc1_ground_init                      false
% 2.66/0.99  --bmc1_pre_inst_next_state              false
% 2.66/0.99  --bmc1_pre_inst_state                   false
% 2.66/0.99  --bmc1_pre_inst_reach_state             false
% 2.66/0.99  --bmc1_out_unsat_core                   false
% 2.66/0.99  --bmc1_aig_witness_out                  false
% 2.66/0.99  --bmc1_verbose                          false
% 2.66/0.99  --bmc1_dump_clauses_tptp                false
% 2.66/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.99  --bmc1_dump_file                        -
% 2.66/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.99  --bmc1_ucm_extend_mode                  1
% 2.66/0.99  --bmc1_ucm_init_mode                    2
% 2.66/0.99  --bmc1_ucm_cone_mode                    none
% 2.66/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.99  --bmc1_ucm_relax_model                  4
% 2.66/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.99  --bmc1_ucm_layered_model                none
% 2.66/0.99  --bmc1_ucm_max_lemma_size               10
% 2.66/0.99  
% 2.66/0.99  ------ AIG Options
% 2.66/0.99  
% 2.66/0.99  --aig_mode                              false
% 2.66/0.99  
% 2.66/0.99  ------ Instantiation Options
% 2.66/0.99  
% 2.66/0.99  --instantiation_flag                    true
% 2.66/0.99  --inst_sos_flag                         false
% 2.66/0.99  --inst_sos_phase                        true
% 2.66/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.99  --inst_lit_sel_side                     none
% 2.66/0.99  --inst_solver_per_active                1400
% 2.66/0.99  --inst_solver_calls_frac                1.
% 2.66/0.99  --inst_passive_queue_type               priority_queues
% 2.66/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.99  --inst_passive_queues_freq              [25;2]
% 2.66/0.99  --inst_dismatching                      true
% 2.66/0.99  --inst_eager_unprocessed_to_passive     true
% 2.66/0.99  --inst_prop_sim_given                   true
% 2.66/0.99  --inst_prop_sim_new                     false
% 2.66/0.99  --inst_subs_new                         false
% 2.66/0.99  --inst_eq_res_simp                      false
% 2.66/0.99  --inst_subs_given                       false
% 2.66/0.99  --inst_orphan_elimination               true
% 2.66/0.99  --inst_learning_loop_flag               true
% 2.66/0.99  --inst_learning_start                   3000
% 2.66/0.99  --inst_learning_factor                  2
% 2.66/0.99  --inst_start_prop_sim_after_learn       3
% 2.66/0.99  --inst_sel_renew                        solver
% 2.66/0.99  --inst_lit_activity_flag                true
% 2.66/0.99  --inst_restr_to_given                   false
% 2.66/0.99  --inst_activity_threshold               500
% 2.66/0.99  --inst_out_proof                        true
% 2.66/0.99  
% 2.66/0.99  ------ Resolution Options
% 2.66/0.99  
% 2.66/0.99  --resolution_flag                       false
% 2.66/0.99  --res_lit_sel                           adaptive
% 2.66/0.99  --res_lit_sel_side                      none
% 2.66/0.99  --res_ordering                          kbo
% 2.66/0.99  --res_to_prop_solver                    active
% 2.66/0.99  --res_prop_simpl_new                    false
% 2.66/0.99  --res_prop_simpl_given                  true
% 2.66/0.99  --res_passive_queue_type                priority_queues
% 2.66/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.99  --res_passive_queues_freq               [15;5]
% 2.66/0.99  --res_forward_subs                      full
% 2.66/0.99  --res_backward_subs                     full
% 2.66/0.99  --res_forward_subs_resolution           true
% 2.66/0.99  --res_backward_subs_resolution          true
% 2.66/0.99  --res_orphan_elimination                true
% 2.66/0.99  --res_time_limit                        2.
% 2.66/0.99  --res_out_proof                         true
% 2.66/0.99  
% 2.66/0.99  ------ Superposition Options
% 2.66/0.99  
% 2.66/0.99  --superposition_flag                    true
% 2.66/0.99  --sup_passive_queue_type                priority_queues
% 2.66/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.99  --demod_completeness_check              fast
% 2.66/0.99  --demod_use_ground                      true
% 2.66/0.99  --sup_to_prop_solver                    passive
% 2.66/0.99  --sup_prop_simpl_new                    true
% 2.66/0.99  --sup_prop_simpl_given                  true
% 2.66/0.99  --sup_fun_splitting                     false
% 2.66/0.99  --sup_smt_interval                      50000
% 2.66/0.99  
% 2.66/0.99  ------ Superposition Simplification Setup
% 2.66/0.99  
% 2.66/0.99  --sup_indices_passive                   []
% 2.66/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_full_bw                           [BwDemod]
% 2.66/0.99  --sup_immed_triv                        [TrivRules]
% 2.66/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_immed_bw_main                     []
% 2.66/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.99  
% 2.66/0.99  ------ Combination Options
% 2.66/0.99  
% 2.66/0.99  --comb_res_mult                         3
% 2.66/0.99  --comb_sup_mult                         2
% 2.66/0.99  --comb_inst_mult                        10
% 2.66/0.99  
% 2.66/0.99  ------ Debug Options
% 2.66/0.99  
% 2.66/0.99  --dbg_backtrace                         false
% 2.66/0.99  --dbg_dump_prop_clauses                 false
% 2.66/0.99  --dbg_dump_prop_clauses_file            -
% 2.66/0.99  --dbg_out_stat                          false
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  ------ Proving...
% 2.66/0.99  
% 2.66/0.99  
% 2.66/0.99  % SZS status Theorem for theBenchmark.p
% 2.66/0.99  
% 2.66/0.99   Resolution empty clause
% 2.66/0.99  
% 2.66/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/0.99  
% 2.66/0.99  fof(f4,axiom,(
% 2.66/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f55,plain,(
% 2.66/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.66/0.99    inference(cnf_transformation,[],[f4])).
% 2.66/0.99  
% 2.66/0.99  fof(f15,axiom,(
% 2.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f34,plain,(
% 2.66/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(ennf_transformation,[],[f15])).
% 2.66/0.99  
% 2.66/0.99  fof(f35,plain,(
% 2.66/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(flattening,[],[f34])).
% 2.66/0.99  
% 2.66/0.99  fof(f46,plain,(
% 2.66/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(nnf_transformation,[],[f35])).
% 2.66/0.99  
% 2.66/0.99  fof(f69,plain,(
% 2.66/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.99    inference(cnf_transformation,[],[f46])).
% 2.66/0.99  
% 2.66/0.99  fof(f16,conjecture,(
% 2.66/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f17,negated_conjecture,(
% 2.66/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.66/0.99    inference(negated_conjecture,[],[f16])).
% 2.66/0.99  
% 2.66/0.99  fof(f36,plain,(
% 2.66/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.66/0.99    inference(ennf_transformation,[],[f17])).
% 2.66/0.99  
% 2.66/0.99  fof(f37,plain,(
% 2.66/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.66/0.99    inference(flattening,[],[f36])).
% 2.66/0.99  
% 2.66/0.99  fof(f48,plain,(
% 2.66/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.66/0.99    introduced(choice_axiom,[])).
% 2.66/0.99  
% 2.66/0.99  fof(f47,plain,(
% 2.66/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.66/0.99    introduced(choice_axiom,[])).
% 2.66/0.99  
% 2.66/0.99  fof(f49,plain,(
% 2.66/0.99    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.66/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f48,f47])).
% 2.66/0.99  
% 2.66/0.99  fof(f79,plain,(
% 2.66/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f80,plain,(
% 2.66/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f13,axiom,(
% 2.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f31,plain,(
% 2.66/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(ennf_transformation,[],[f13])).
% 2.66/0.99  
% 2.66/0.99  fof(f67,plain,(
% 2.66/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.99    inference(cnf_transformation,[],[f31])).
% 2.66/0.99  
% 2.66/0.99  fof(f76,plain,(
% 2.66/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f77,plain,(
% 2.66/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f9,axiom,(
% 2.66/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f26,plain,(
% 2.66/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/0.99    inference(ennf_transformation,[],[f9])).
% 2.66/0.99  
% 2.66/0.99  fof(f27,plain,(
% 2.66/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/0.99    inference(flattening,[],[f26])).
% 2.66/0.99  
% 2.66/0.99  fof(f44,plain,(
% 2.66/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.66/0.99    introduced(choice_axiom,[])).
% 2.66/0.99  
% 2.66/0.99  fof(f45,plain,(
% 2.66/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f44])).
% 2.66/0.99  
% 2.66/0.99  fof(f62,plain,(
% 2.66/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.99    inference(cnf_transformation,[],[f45])).
% 2.66/0.99  
% 2.66/0.99  fof(f78,plain,(
% 2.66/0.99    v1_funct_1(sK5)),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f10,axiom,(
% 2.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f28,plain,(
% 2.66/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(ennf_transformation,[],[f10])).
% 2.66/0.99  
% 2.66/0.99  fof(f64,plain,(
% 2.66/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.99    inference(cnf_transformation,[],[f28])).
% 2.66/0.99  
% 2.66/0.99  fof(f75,plain,(
% 2.66/0.99    v1_funct_1(sK4)),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f81,plain,(
% 2.66/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f63,plain,(
% 2.66/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.99    inference(cnf_transformation,[],[f45])).
% 2.66/0.99  
% 2.66/0.99  fof(f14,axiom,(
% 2.66/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f32,plain,(
% 2.66/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.66/0.99    inference(ennf_transformation,[],[f14])).
% 2.66/0.99  
% 2.66/0.99  fof(f33,plain,(
% 2.66/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.99    inference(flattening,[],[f32])).
% 2.66/0.99  
% 2.66/0.99  fof(f68,plain,(
% 2.66/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.99    inference(cnf_transformation,[],[f33])).
% 2.66/0.99  
% 2.66/0.99  fof(f82,plain,(
% 2.66/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.66/0.99    inference(cnf_transformation,[],[f49])).
% 2.66/0.99  
% 2.66/0.99  fof(f1,axiom,(
% 2.66/0.99    v1_xboole_0(k1_xboole_0)),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f50,plain,(
% 2.66/0.99    v1_xboole_0(k1_xboole_0)),
% 2.66/0.99    inference(cnf_transformation,[],[f1])).
% 2.66/0.99  
% 2.66/0.99  fof(f2,axiom,(
% 2.66/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f20,plain,(
% 2.66/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.66/0.99    inference(ennf_transformation,[],[f2])).
% 2.66/0.99  
% 2.66/0.99  fof(f51,plain,(
% 2.66/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.66/0.99    inference(cnf_transformation,[],[f20])).
% 2.66/0.99  
% 2.66/0.99  fof(f12,axiom,(
% 2.66/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.99  
% 2.66/0.99  fof(f30,plain,(
% 2.66/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.66/0.99    inference(ennf_transformation,[],[f12])).
% 2.66/0.99  
% 2.66/0.99  fof(f66,plain,(
% 2.66/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.66/0.99    inference(cnf_transformation,[],[f30])).
% 2.66/0.99  
% 2.66/0.99  cnf(c_5,plain,
% 2.66/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.66/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1097,plain,
% 2.66/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_24,plain,
% 2.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.66/0.99      | k1_xboole_0 = X2 ),
% 2.66/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_28,negated_conjecture,
% 2.66/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.66/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_450,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.66/0.99      | sK5 != X0
% 2.66/0.99      | sK3 != X2
% 2.66/0.99      | sK2 != X1
% 2.66/0.99      | k1_xboole_0 = X2 ),
% 2.66/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_451,plain,
% 2.66/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.66/0.99      | k1_xboole_0 = sK3 ),
% 2.66/0.99      inference(unflattening,[status(thm)],[c_450]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_27,negated_conjecture,
% 2.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.66/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_453,plain,
% 2.66/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.66/0.99      inference(global_propositional_subsumption,[status(thm)],[c_451,c_27]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1085,plain,
% 2.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_17,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1087,plain,
% 2.66/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.66/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_2046,plain,
% 2.66/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_1085,c_1087]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_2195,plain,
% 2.66/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_453,c_2046]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_31,negated_conjecture,
% 2.66/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.66/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_461,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.66/0.99      | sK4 != X0
% 2.66/0.99      | sK3 != X2
% 2.66/0.99      | sK2 != X1
% 2.66/0.99      | k1_xboole_0 = X2 ),
% 2.66/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_462,plain,
% 2.66/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.66/0.99      | k1_xboole_0 = sK3 ),
% 2.66/0.99      inference(unflattening,[status(thm)],[c_461]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_30,negated_conjecture,
% 2.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.66/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_464,plain,
% 2.66/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.66/0.99      inference(global_propositional_subsumption,[status(thm)],[c_462,c_30]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1083,plain,
% 2.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_2047,plain,
% 2.66/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_1083,c_1087]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_2198,plain,
% 2.66/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_464,c_2047]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_13,plain,
% 2.66/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.66/0.99      | ~ v1_funct_1(X1)
% 2.66/0.99      | ~ v1_funct_1(X0)
% 2.66/0.99      | ~ v1_relat_1(X1)
% 2.66/0.99      | ~ v1_relat_1(X0)
% 2.66/0.99      | X0 = X1
% 2.66/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1090,plain,
% 2.66/0.99      ( X0 = X1
% 2.66/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.66/0.99      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.66/0.99      | v1_funct_1(X1) != iProver_top
% 2.66/0.99      | v1_funct_1(X0) != iProver_top
% 2.66/0.99      | v1_relat_1(X0) != iProver_top
% 2.66/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3138,plain,
% 2.66/0.99      ( k1_relat_1(X0) != sK2
% 2.66/0.99      | sK5 = X0
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.66/0.99      | v1_funct_1(X0) != iProver_top
% 2.66/0.99      | v1_funct_1(sK5) != iProver_top
% 2.66/0.99      | v1_relat_1(X0) != iProver_top
% 2.66/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_2195,c_1090]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_29,negated_conjecture,
% 2.66/0.99      ( v1_funct_1(sK5) ),
% 2.66/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_36,plain,
% 2.66/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_38,plain,
% 2.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_14,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1333,plain,
% 2.66/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | v1_relat_1(sK5) ),
% 2.66/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1334,plain,
% 2.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.66/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3413,plain,
% 2.66/0.99      ( v1_relat_1(X0) != iProver_top
% 2.66/0.99      | k1_relat_1(X0) != sK2
% 2.66/0.99      | sK5 = X0
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.66/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.66/0.99      inference(global_propositional_subsumption,
% 2.66/0.99                [status(thm)],
% 2.66/0.99                [c_3138,c_36,c_38,c_1334]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3414,plain,
% 2.66/0.99      ( k1_relat_1(X0) != sK2
% 2.66/0.99      | sK5 = X0
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.66/0.99      | v1_funct_1(X0) != iProver_top
% 2.66/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.66/0.99      inference(renaming,[status(thm)],[c_3413]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3426,plain,
% 2.66/0.99      ( sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.66/0.99      | v1_funct_1(sK4) != iProver_top
% 2.66/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_2198,c_3414]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_32,negated_conjecture,
% 2.66/0.99      ( v1_funct_1(sK4) ),
% 2.66/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_33,plain,
% 2.66/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_35,plain,
% 2.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1336,plain,
% 2.66/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | v1_relat_1(sK4) ),
% 2.66/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1337,plain,
% 2.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.66/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3439,plain,
% 2.66/0.99      ( sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.66/0.99      inference(global_propositional_subsumption,
% 2.66/0.99                [status(thm)],
% 2.66/0.99                [c_3426,c_33,c_35,c_1337]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3446,plain,
% 2.66/0.99      ( sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_2198,c_3439]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_26,negated_conjecture,
% 2.66/0.99      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1086,plain,
% 2.66/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.66/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3495,plain,
% 2.66/0.99      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.66/0.99      | sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_3446,c_1086]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_12,plain,
% 2.66/0.99      ( ~ v1_funct_1(X0)
% 2.66/0.99      | ~ v1_funct_1(X1)
% 2.66/0.99      | ~ v1_relat_1(X0)
% 2.66/0.99      | ~ v1_relat_1(X1)
% 2.66/0.99      | X1 = X0
% 2.66/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.66/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.66/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1091,plain,
% 2.66/0.99      ( X0 = X1
% 2.66/0.99      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.66/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.66/0.99      | v1_funct_1(X0) != iProver_top
% 2.66/0.99      | v1_funct_1(X1) != iProver_top
% 2.66/0.99      | v1_relat_1(X1) != iProver_top
% 2.66/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3721,plain,
% 2.66/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.66/0.99      | sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0
% 2.66/0.99      | v1_funct_1(sK5) != iProver_top
% 2.66/0.99      | v1_funct_1(sK4) != iProver_top
% 2.66/0.99      | v1_relat_1(sK5) != iProver_top
% 2.66/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_3495,c_1091]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_3738,plain,
% 2.66/0.99      ( ~ v1_funct_1(sK5)
% 2.66/0.99      | ~ v1_funct_1(sK4)
% 2.66/0.99      | ~ v1_relat_1(sK5)
% 2.66/0.99      | ~ v1_relat_1(sK4)
% 2.66/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.66/0.99      | sK5 = sK4
% 2.66/0.99      | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3721]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_4292,plain,
% 2.66/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(global_propositional_subsumption,
% 2.66/0.99                [status(thm)],
% 2.66/0.99                [c_3721,c_33,c_35,c_36,c_38,c_1334,c_1337]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_4297,plain,
% 2.66/0.99      ( k1_relat_1(sK4) != sK2 | sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_2195,c_4292]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_4537,plain,
% 2.66/0.99      ( sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.66/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4297,c_2198]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_18,plain,
% 2.66/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.66/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_25,negated_conjecture,
% 2.66/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.66/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_335,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | sK5 != X0
% 2.66/0.99      | sK4 != X0
% 2.66/0.99      | sK3 != X2
% 2.66/0.99      | sK2 != X1 ),
% 2.66/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_336,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.99      | sK4 != sK5 ),
% 2.66/0.99      inference(unflattening,[status(thm)],[c_335]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_340,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | sK4 != sK5 ),
% 2.66/0.99      inference(global_propositional_subsumption,[status(thm)],[c_336,c_27]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1081,plain,
% 2.66/0.99      ( sK4 != sK5
% 2.66/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_4553,plain,
% 2.66/0.99      ( sK3 = k1_xboole_0
% 2.66/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.66/0.99      inference(superposition,[status(thm)],[c_4537,c_1081]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_0,plain,
% 2.66/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_342,plain,
% 2.66/0.99      ( sK4 != sK5
% 2.66/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.66/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1,plain,
% 2.66/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.66/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1306,plain,
% 2.66/0.99      ( ~ v1_xboole_0(sK5) | ~ v1_xboole_0(sK4) | sK4 = sK5 ),
% 2.66/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_658,plain,
% 2.66/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.66/0.99      theory(equality) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1584,plain,
% 2.66/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 2.66/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1586,plain,
% 2.66/0.99      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 2.66/0.99      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_16,plain,
% 2.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.99      | ~ v1_xboole_0(X2)
% 2.66/0.99      | v1_xboole_0(X0) ),
% 2.66/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.66/0.99  
% 2.66/0.99  cnf(c_1088,plain,
% 2.66/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.66/1.00      | v1_xboole_0(X2) != iProver_top
% 2.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2567,plain,
% 2.66/1.00      ( v1_xboole_0(sK5) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1085,c_1088]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2592,plain,
% 2.66/1.00      ( v1_xboole_0(sK5) | ~ v1_xboole_0(sK3) ),
% 2.66/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2568,plain,
% 2.66/1.00      ( v1_xboole_0(sK4) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1083,c_1088]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2593,plain,
% 2.66/1.00      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK3) ),
% 2.66/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2568]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4576,plain,
% 2.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_4553,c_0,c_342,c_1306,c_1586,c_2592,c_2593]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4583,plain,
% 2.66/1.00      ( $false ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1097,c_4576]) ).
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  ------                               Statistics
% 2.66/1.00  
% 2.66/1.00  ------ General
% 2.66/1.00  
% 2.66/1.00  abstr_ref_over_cycles:                  0
% 2.66/1.00  abstr_ref_under_cycles:                 0
% 2.66/1.00  gc_basic_clause_elim:                   0
% 2.66/1.00  forced_gc_time:                         0
% 2.66/1.00  parsing_time:                           0.008
% 2.66/1.00  unif_index_cands_time:                  0.
% 2.66/1.00  unif_index_add_time:                    0.
% 2.66/1.00  orderings_time:                         0.
% 2.66/1.00  out_proof_time:                         0.012
% 2.66/1.00  total_time:                             0.129
% 2.66/1.00  num_of_symbols:                         52
% 2.66/1.00  num_of_terms:                           4288
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing
% 2.66/1.00  
% 2.66/1.00  num_of_splits:                          0
% 2.66/1.00  num_of_split_atoms:                     0
% 2.66/1.00  num_of_reused_defs:                     0
% 2.66/1.00  num_eq_ax_congr_red:                    22
% 2.66/1.00  num_of_sem_filtered_clauses:            1
% 2.66/1.00  num_of_subtypes:                        0
% 2.66/1.00  monotx_restored_types:                  0
% 2.66/1.00  sat_num_of_epr_types:                   0
% 2.66/1.00  sat_num_of_non_cyclic_types:            0
% 2.66/1.00  sat_guarded_non_collapsed_types:        0
% 2.66/1.00  num_pure_diseq_elim:                    0
% 2.66/1.00  simp_replaced_by:                       0
% 2.66/1.00  res_preprocessed:                       143
% 2.66/1.00  prep_upred:                             0
% 2.66/1.00  prep_unflattend:                        37
% 2.66/1.00  smt_new_axioms:                         0
% 2.66/1.00  pred_elim_cands:                        5
% 2.66/1.00  pred_elim:                              3
% 2.66/1.00  pred_elim_cl:                           4
% 2.66/1.00  pred_elim_cycles:                       5
% 2.66/1.00  merged_defs:                            0
% 2.66/1.00  merged_defs_ncl:                        0
% 2.66/1.00  bin_hyper_res:                          0
% 2.66/1.00  prep_cycles:                            4
% 2.66/1.00  pred_elim_time:                         0.002
% 2.66/1.00  splitting_time:                         0.
% 2.66/1.00  sem_filter_time:                        0.
% 2.66/1.00  monotx_time:                            0.
% 2.66/1.00  subtype_inf_time:                       0.
% 2.66/1.00  
% 2.66/1.00  ------ Problem properties
% 2.66/1.00  
% 2.66/1.00  clauses:                                29
% 2.66/1.00  conjectures:                            5
% 2.66/1.00  epr:                                    4
% 2.66/1.00  horn:                                   23
% 2.66/1.00  ground:                                 11
% 2.66/1.00  unary:                                  9
% 2.66/1.00  binary:                                 7
% 2.66/1.00  lits:                                   73
% 2.66/1.00  lits_eq:                                29
% 2.66/1.00  fd_pure:                                0
% 2.66/1.00  fd_pseudo:                              0
% 2.66/1.00  fd_cond:                                1
% 2.66/1.00  fd_pseudo_cond:                         3
% 2.66/1.00  ac_symbols:                             0
% 2.66/1.00  
% 2.66/1.00  ------ Propositional Solver
% 2.66/1.00  
% 2.66/1.00  prop_solver_calls:                      26
% 2.66/1.00  prop_fast_solver_calls:                 966
% 2.66/1.00  smt_solver_calls:                       0
% 2.66/1.00  smt_fast_solver_calls:                  0
% 2.66/1.00  prop_num_of_clauses:                    1685
% 2.66/1.00  prop_preprocess_simplified:             5337
% 2.66/1.00  prop_fo_subsumed:                       22
% 2.66/1.00  prop_solver_time:                       0.
% 2.66/1.00  smt_solver_time:                        0.
% 2.66/1.00  smt_fast_solver_time:                   0.
% 2.66/1.00  prop_fast_solver_time:                  0.
% 2.66/1.00  prop_unsat_core_time:                   0.
% 2.66/1.00  
% 2.66/1.00  ------ QBF
% 2.66/1.00  
% 2.66/1.00  qbf_q_res:                              0
% 2.66/1.00  qbf_num_tautologies:                    0
% 2.66/1.00  qbf_prep_cycles:                        0
% 2.66/1.00  
% 2.66/1.00  ------ BMC1
% 2.66/1.00  
% 2.66/1.00  bmc1_current_bound:                     -1
% 2.66/1.00  bmc1_last_solved_bound:                 -1
% 2.66/1.00  bmc1_unsat_core_size:                   -1
% 2.66/1.00  bmc1_unsat_core_parents_size:           -1
% 2.66/1.00  bmc1_merge_next_fun:                    0
% 2.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation
% 2.66/1.00  
% 2.66/1.00  inst_num_of_clauses:                    605
% 2.66/1.00  inst_num_in_passive:                    32
% 2.66/1.00  inst_num_in_active:                     333
% 2.66/1.00  inst_num_in_unprocessed:                240
% 2.66/1.00  inst_num_of_loops:                      350
% 2.66/1.00  inst_num_of_learning_restarts:          0
% 2.66/1.00  inst_num_moves_active_passive:          14
% 2.66/1.00  inst_lit_activity:                      0
% 2.66/1.00  inst_lit_activity_moves:                0
% 2.66/1.00  inst_num_tautologies:                   0
% 2.66/1.00  inst_num_prop_implied:                  0
% 2.66/1.00  inst_num_existing_simplified:           0
% 2.66/1.00  inst_num_eq_res_simplified:             0
% 2.66/1.00  inst_num_child_elim:                    0
% 2.66/1.00  inst_num_of_dismatching_blockings:      204
% 2.66/1.00  inst_num_of_non_proper_insts:           744
% 2.66/1.00  inst_num_of_duplicates:                 0
% 2.66/1.00  inst_inst_num_from_inst_to_res:         0
% 2.66/1.00  inst_dismatching_checking_time:         0.
% 2.66/1.00  
% 2.66/1.00  ------ Resolution
% 2.66/1.00  
% 2.66/1.00  res_num_of_clauses:                     0
% 2.66/1.00  res_num_in_passive:                     0
% 2.66/1.00  res_num_in_active:                      0
% 2.66/1.00  res_num_of_loops:                       147
% 2.66/1.00  res_forward_subset_subsumed:            36
% 2.66/1.00  res_backward_subset_subsumed:           0
% 2.66/1.00  res_forward_subsumed:                   0
% 2.66/1.00  res_backward_subsumed:                  0
% 2.66/1.00  res_forward_subsumption_resolution:     0
% 2.66/1.00  res_backward_subsumption_resolution:    0
% 2.66/1.00  res_clause_to_clause_subsumption:       106
% 2.66/1.00  res_orphan_elimination:                 0
% 2.66/1.00  res_tautology_del:                      46
% 2.66/1.00  res_num_eq_res_simplified:              0
% 2.66/1.00  res_num_sel_changes:                    0
% 2.66/1.00  res_moves_from_active_to_pass:          0
% 2.66/1.00  
% 2.66/1.00  ------ Superposition
% 2.66/1.00  
% 2.66/1.00  sup_time_total:                         0.
% 2.66/1.00  sup_time_generating:                    0.
% 2.66/1.00  sup_time_sim_full:                      0.
% 2.66/1.00  sup_time_sim_immed:                     0.
% 2.66/1.00  
% 2.66/1.00  sup_num_of_clauses:                     82
% 2.66/1.00  sup_num_in_active:                      67
% 2.66/1.00  sup_num_in_passive:                     15
% 2.66/1.00  sup_num_of_loops:                       69
% 2.66/1.00  sup_fw_superposition:                   75
% 2.66/1.00  sup_bw_superposition:                   25
% 2.66/1.00  sup_immediate_simplified:               19
% 2.66/1.00  sup_given_eliminated:                   0
% 2.66/1.00  comparisons_done:                       0
% 2.66/1.00  comparisons_avoided:                    30
% 2.66/1.00  
% 2.66/1.00  ------ Simplifications
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  sim_fw_subset_subsumed:                 8
% 2.66/1.00  sim_bw_subset_subsumed:                 3
% 2.66/1.00  sim_fw_subsumed:                        6
% 2.66/1.00  sim_bw_subsumed:                        0
% 2.66/1.00  sim_fw_subsumption_res:                 0
% 2.66/1.00  sim_bw_subsumption_res:                 0
% 2.66/1.00  sim_tautology_del:                      7
% 2.66/1.00  sim_eq_tautology_del:                   6
% 2.66/1.00  sim_eq_res_simp:                        0
% 2.66/1.00  sim_fw_demodulated:                     5
% 2.66/1.00  sim_bw_demodulated:                     0
% 2.66/1.00  sim_light_normalised:                   6
% 2.66/1.00  sim_joinable_taut:                      0
% 2.66/1.00  sim_joinable_simp:                      0
% 2.66/1.00  sim_ac_normalised:                      0
% 2.66/1.00  sim_smt_subsumption:                    0
% 2.66/1.00  
%------------------------------------------------------------------------------
