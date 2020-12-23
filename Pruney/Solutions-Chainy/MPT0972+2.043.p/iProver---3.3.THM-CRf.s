%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:16 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  124 (1213 expanded)
%              Number of clauses        :   75 ( 381 expanded)
%              Number of leaves         :   14 ( 298 expanded)
%              Depth                    :   25
%              Number of atoms          :  441 (7458 expanded)
%              Number of equality atoms :  208 (1585 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36,f35])).

fof(f63,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f66,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_450,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_452,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_23])).

cnf(c_1058,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1060,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1446,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1058,c_1060])).

cnf(c_1626,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_452,c_1446])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_463,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_26])).

cnf(c_1056,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1447,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1056,c_1060])).

cnf(c_1702,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_463,c_1447])).

cnf(c_10,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1062,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2397,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1062])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_696,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1428,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_1429,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_1431,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1643,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_2082,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1061,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1932,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1061])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_291,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1242,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1243,plain,
    ( sK3 = sK4
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_1933,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1061])).

cnf(c_2168,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_23,c_291,c_1243,c_1933])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2533,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2534,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(c_2835,plain,
    ( v1_relat_1(X0) != iProver_top
    | sK4 = X0
    | k1_relat_1(X0) != sK1
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2397,c_32,c_23,c_34,c_88,c_291,c_1243,c_1431,c_1932,c_1933,c_2082,c_2534])).

cnf(c_2836,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2835])).

cnf(c_2847,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_2836])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1638,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2073,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_2074,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2073])).

cnf(c_2860,plain,
    ( sK4 = sK3
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2847,c_29,c_31,c_23,c_88,c_291,c_1243,c_1431,c_1932,c_1933,c_2074,c_2534])).

cnf(c_2866,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_2860])).

cnf(c_2923,plain,
    ( sK4 = sK3
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2866,c_23,c_88,c_291,c_1243,c_1431,c_1932,c_1933])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1059,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2929,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_2923,c_1059])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1063,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2932,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_1063])).

cnf(c_2933,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2932])).

cnf(c_3053,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2932,c_28,c_26,c_25,c_23,c_2073,c_2081,c_2533,c_2933])).

cnf(c_3057,plain,
    ( k1_relat_1(sK3) != sK1
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1626,c_3053])).

cnf(c_3133,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3057,c_23,c_88,c_291,c_1243,c_1431,c_1702,c_1932,c_1933])).

cnf(c_293,plain,
    ( sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_23])).

cnf(c_3150,plain,
    ( sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_3133,c_293])).

cnf(c_3151,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3150])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.93/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.93/1.02  
% 0.93/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.93/1.02  
% 0.93/1.02  ------  iProver source info
% 0.93/1.02  
% 0.93/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.93/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.93/1.02  git: non_committed_changes: false
% 0.93/1.02  git: last_make_outside_of_git: false
% 0.93/1.02  
% 0.93/1.02  ------ 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options
% 0.93/1.02  
% 0.93/1.02  --out_options                           all
% 0.93/1.02  --tptp_safe_out                         true
% 0.93/1.02  --problem_path                          ""
% 0.93/1.02  --include_path                          ""
% 0.93/1.02  --clausifier                            res/vclausify_rel
% 0.93/1.02  --clausifier_options                    --mode clausify
% 0.93/1.02  --stdin                                 false
% 0.93/1.02  --stats_out                             all
% 0.93/1.02  
% 0.93/1.02  ------ General Options
% 0.93/1.02  
% 0.93/1.02  --fof                                   false
% 0.93/1.02  --time_out_real                         305.
% 0.93/1.02  --time_out_virtual                      -1.
% 0.93/1.02  --symbol_type_check                     false
% 0.93/1.02  --clausify_out                          false
% 0.93/1.02  --sig_cnt_out                           false
% 0.93/1.02  --trig_cnt_out                          false
% 0.93/1.02  --trig_cnt_out_tolerance                1.
% 0.93/1.02  --trig_cnt_out_sk_spl                   false
% 0.93/1.02  --abstr_cl_out                          false
% 0.93/1.02  
% 0.93/1.02  ------ Global Options
% 0.93/1.02  
% 0.93/1.02  --schedule                              default
% 0.93/1.02  --add_important_lit                     false
% 0.93/1.02  --prop_solver_per_cl                    1000
% 0.93/1.02  --min_unsat_core                        false
% 0.93/1.02  --soft_assumptions                      false
% 0.93/1.02  --soft_lemma_size                       3
% 0.93/1.02  --prop_impl_unit_size                   0
% 0.93/1.02  --prop_impl_unit                        []
% 0.93/1.02  --share_sel_clauses                     true
% 0.93/1.02  --reset_solvers                         false
% 0.93/1.02  --bc_imp_inh                            [conj_cone]
% 0.93/1.02  --conj_cone_tolerance                   3.
% 0.93/1.02  --extra_neg_conj                        none
% 0.93/1.02  --large_theory_mode                     true
% 0.93/1.02  --prolific_symb_bound                   200
% 0.93/1.02  --lt_threshold                          2000
% 0.93/1.02  --clause_weak_htbl                      true
% 0.93/1.02  --gc_record_bc_elim                     false
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing Options
% 0.93/1.02  
% 0.93/1.02  --preprocessing_flag                    true
% 0.93/1.02  --time_out_prep_mult                    0.1
% 0.93/1.02  --splitting_mode                        input
% 0.93/1.02  --splitting_grd                         true
% 0.93/1.02  --splitting_cvd                         false
% 0.93/1.02  --splitting_cvd_svl                     false
% 0.93/1.02  --splitting_nvd                         32
% 0.93/1.02  --sub_typing                            true
% 0.93/1.02  --prep_gs_sim                           true
% 0.93/1.02  --prep_unflatten                        true
% 0.93/1.02  --prep_res_sim                          true
% 0.93/1.02  --prep_upred                            true
% 0.93/1.02  --prep_sem_filter                       exhaustive
% 0.93/1.02  --prep_sem_filter_out                   false
% 0.93/1.02  --pred_elim                             true
% 0.93/1.02  --res_sim_input                         true
% 0.93/1.02  --eq_ax_congr_red                       true
% 0.93/1.02  --pure_diseq_elim                       true
% 0.93/1.02  --brand_transform                       false
% 0.93/1.02  --non_eq_to_eq                          false
% 0.93/1.02  --prep_def_merge                        true
% 0.93/1.02  --prep_def_merge_prop_impl              false
% 0.93/1.02  --prep_def_merge_mbd                    true
% 0.93/1.02  --prep_def_merge_tr_red                 false
% 0.93/1.02  --prep_def_merge_tr_cl                  false
% 0.93/1.02  --smt_preprocessing                     true
% 0.93/1.02  --smt_ac_axioms                         fast
% 0.93/1.02  --preprocessed_out                      false
% 0.93/1.02  --preprocessed_stats                    false
% 0.93/1.02  
% 0.93/1.02  ------ Abstraction refinement Options
% 0.93/1.02  
% 0.93/1.02  --abstr_ref                             []
% 0.93/1.02  --abstr_ref_prep                        false
% 0.93/1.02  --abstr_ref_until_sat                   false
% 0.93/1.02  --abstr_ref_sig_restrict                funpre
% 0.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.02  --abstr_ref_under                       []
% 0.93/1.02  
% 0.93/1.02  ------ SAT Options
% 0.93/1.02  
% 0.93/1.02  --sat_mode                              false
% 0.93/1.02  --sat_fm_restart_options                ""
% 0.93/1.02  --sat_gr_def                            false
% 0.93/1.02  --sat_epr_types                         true
% 0.93/1.02  --sat_non_cyclic_types                  false
% 0.93/1.02  --sat_finite_models                     false
% 0.93/1.02  --sat_fm_lemmas                         false
% 0.93/1.02  --sat_fm_prep                           false
% 0.93/1.02  --sat_fm_uc_incr                        true
% 0.93/1.02  --sat_out_model                         small
% 0.93/1.02  --sat_out_clauses                       false
% 0.93/1.02  
% 0.93/1.02  ------ QBF Options
% 0.93/1.02  
% 0.93/1.02  --qbf_mode                              false
% 0.93/1.02  --qbf_elim_univ                         false
% 0.93/1.02  --qbf_dom_inst                          none
% 0.93/1.02  --qbf_dom_pre_inst                      false
% 0.93/1.02  --qbf_sk_in                             false
% 0.93/1.02  --qbf_pred_elim                         true
% 0.93/1.02  --qbf_split                             512
% 0.93/1.02  
% 0.93/1.02  ------ BMC1 Options
% 0.93/1.02  
% 0.93/1.02  --bmc1_incremental                      false
% 0.93/1.02  --bmc1_axioms                           reachable_all
% 0.93/1.02  --bmc1_min_bound                        0
% 0.93/1.02  --bmc1_max_bound                        -1
% 0.93/1.02  --bmc1_max_bound_default                -1
% 0.93/1.02  --bmc1_symbol_reachability              true
% 0.93/1.02  --bmc1_property_lemmas                  false
% 0.93/1.02  --bmc1_k_induction                      false
% 0.93/1.02  --bmc1_non_equiv_states                 false
% 0.93/1.02  --bmc1_deadlock                         false
% 0.93/1.02  --bmc1_ucm                              false
% 0.93/1.02  --bmc1_add_unsat_core                   none
% 0.93/1.02  --bmc1_unsat_core_children              false
% 0.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.02  --bmc1_out_stat                         full
% 0.93/1.02  --bmc1_ground_init                      false
% 0.93/1.02  --bmc1_pre_inst_next_state              false
% 0.93/1.02  --bmc1_pre_inst_state                   false
% 0.93/1.02  --bmc1_pre_inst_reach_state             false
% 0.93/1.02  --bmc1_out_unsat_core                   false
% 0.93/1.02  --bmc1_aig_witness_out                  false
% 0.93/1.02  --bmc1_verbose                          false
% 0.93/1.02  --bmc1_dump_clauses_tptp                false
% 0.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.02  --bmc1_dump_file                        -
% 0.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.02  --bmc1_ucm_extend_mode                  1
% 0.93/1.02  --bmc1_ucm_init_mode                    2
% 0.93/1.02  --bmc1_ucm_cone_mode                    none
% 0.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.02  --bmc1_ucm_relax_model                  4
% 0.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.02  --bmc1_ucm_layered_model                none
% 0.93/1.02  --bmc1_ucm_max_lemma_size               10
% 0.93/1.02  
% 0.93/1.02  ------ AIG Options
% 0.93/1.02  
% 0.93/1.02  --aig_mode                              false
% 0.93/1.02  
% 0.93/1.02  ------ Instantiation Options
% 0.93/1.02  
% 0.93/1.02  --instantiation_flag                    true
% 0.93/1.02  --inst_sos_flag                         false
% 0.93/1.02  --inst_sos_phase                        true
% 0.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel_side                     num_symb
% 0.93/1.02  --inst_solver_per_active                1400
% 0.93/1.02  --inst_solver_calls_frac                1.
% 0.93/1.02  --inst_passive_queue_type               priority_queues
% 0.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.02  --inst_passive_queues_freq              [25;2]
% 0.93/1.02  --inst_dismatching                      true
% 0.93/1.02  --inst_eager_unprocessed_to_passive     true
% 0.93/1.02  --inst_prop_sim_given                   true
% 0.93/1.02  --inst_prop_sim_new                     false
% 0.93/1.02  --inst_subs_new                         false
% 0.93/1.02  --inst_eq_res_simp                      false
% 0.93/1.02  --inst_subs_given                       false
% 0.93/1.02  --inst_orphan_elimination               true
% 0.93/1.02  --inst_learning_loop_flag               true
% 0.93/1.02  --inst_learning_start                   3000
% 0.93/1.02  --inst_learning_factor                  2
% 0.93/1.02  --inst_start_prop_sim_after_learn       3
% 0.93/1.02  --inst_sel_renew                        solver
% 0.93/1.02  --inst_lit_activity_flag                true
% 0.93/1.02  --inst_restr_to_given                   false
% 0.93/1.02  --inst_activity_threshold               500
% 0.93/1.02  --inst_out_proof                        true
% 0.93/1.02  
% 0.93/1.02  ------ Resolution Options
% 0.93/1.02  
% 0.93/1.02  --resolution_flag                       true
% 0.93/1.02  --res_lit_sel                           adaptive
% 0.93/1.02  --res_lit_sel_side                      none
% 0.93/1.02  --res_ordering                          kbo
% 0.93/1.02  --res_to_prop_solver                    active
% 0.93/1.02  --res_prop_simpl_new                    false
% 0.93/1.02  --res_prop_simpl_given                  true
% 0.93/1.02  --res_passive_queue_type                priority_queues
% 0.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.02  --res_passive_queues_freq               [15;5]
% 0.93/1.02  --res_forward_subs                      full
% 0.93/1.02  --res_backward_subs                     full
% 0.93/1.02  --res_forward_subs_resolution           true
% 0.93/1.02  --res_backward_subs_resolution          true
% 0.93/1.02  --res_orphan_elimination                true
% 0.93/1.02  --res_time_limit                        2.
% 0.93/1.02  --res_out_proof                         true
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Options
% 0.93/1.02  
% 0.93/1.02  --superposition_flag                    true
% 0.93/1.02  --sup_passive_queue_type                priority_queues
% 0.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.02  --demod_completeness_check              fast
% 0.93/1.02  --demod_use_ground                      true
% 0.93/1.02  --sup_to_prop_solver                    passive
% 0.93/1.02  --sup_prop_simpl_new                    true
% 0.93/1.02  --sup_prop_simpl_given                  true
% 0.93/1.02  --sup_fun_splitting                     false
% 0.93/1.02  --sup_smt_interval                      50000
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Simplification Setup
% 0.93/1.02  
% 0.93/1.02  --sup_indices_passive                   []
% 0.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_full_bw                           [BwDemod]
% 0.93/1.02  --sup_immed_triv                        [TrivRules]
% 0.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_immed_bw_main                     []
% 0.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  
% 0.93/1.02  ------ Combination Options
% 0.93/1.02  
% 0.93/1.02  --comb_res_mult                         3
% 0.93/1.02  --comb_sup_mult                         2
% 0.93/1.02  --comb_inst_mult                        10
% 0.93/1.02  
% 0.93/1.02  ------ Debug Options
% 0.93/1.02  
% 0.93/1.02  --dbg_backtrace                         false
% 0.93/1.02  --dbg_dump_prop_clauses                 false
% 0.93/1.02  --dbg_dump_prop_clauses_file            -
% 0.93/1.02  --dbg_out_stat                          false
% 0.93/1.02  ------ Parsing...
% 0.93/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.93/1.02  ------ Proving...
% 0.93/1.02  ------ Problem Properties 
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  clauses                                 25
% 0.93/1.02  conjectures                             5
% 0.93/1.02  EPR                                     5
% 0.93/1.02  Horn                                    19
% 0.93/1.02  unary                                   10
% 0.93/1.02  binary                                  4
% 0.93/1.02  lits                                    61
% 0.93/1.02  lits eq                                 28
% 0.93/1.02  fd_pure                                 0
% 0.93/1.02  fd_pseudo                               0
% 0.93/1.02  fd_cond                                 1
% 0.93/1.02  fd_pseudo_cond                          3
% 0.93/1.02  AC symbols                              0
% 0.93/1.02  
% 0.93/1.02  ------ Schedule dynamic 5 is on 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  ------ 
% 0.93/1.02  Current options:
% 0.93/1.02  ------ 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options
% 0.93/1.02  
% 0.93/1.02  --out_options                           all
% 0.93/1.02  --tptp_safe_out                         true
% 0.93/1.02  --problem_path                          ""
% 0.93/1.02  --include_path                          ""
% 0.93/1.02  --clausifier                            res/vclausify_rel
% 0.93/1.02  --clausifier_options                    --mode clausify
% 0.93/1.02  --stdin                                 false
% 0.93/1.02  --stats_out                             all
% 0.93/1.02  
% 0.93/1.02  ------ General Options
% 0.93/1.02  
% 0.93/1.02  --fof                                   false
% 0.93/1.02  --time_out_real                         305.
% 0.93/1.02  --time_out_virtual                      -1.
% 0.93/1.02  --symbol_type_check                     false
% 0.93/1.02  --clausify_out                          false
% 0.93/1.02  --sig_cnt_out                           false
% 0.93/1.02  --trig_cnt_out                          false
% 0.93/1.02  --trig_cnt_out_tolerance                1.
% 0.93/1.02  --trig_cnt_out_sk_spl                   false
% 0.93/1.02  --abstr_cl_out                          false
% 0.93/1.02  
% 0.93/1.02  ------ Global Options
% 0.93/1.02  
% 0.93/1.02  --schedule                              default
% 0.93/1.02  --add_important_lit                     false
% 0.93/1.02  --prop_solver_per_cl                    1000
% 0.93/1.02  --min_unsat_core                        false
% 0.93/1.02  --soft_assumptions                      false
% 0.93/1.02  --soft_lemma_size                       3
% 0.93/1.02  --prop_impl_unit_size                   0
% 0.93/1.02  --prop_impl_unit                        []
% 0.93/1.02  --share_sel_clauses                     true
% 0.93/1.02  --reset_solvers                         false
% 0.93/1.02  --bc_imp_inh                            [conj_cone]
% 0.93/1.02  --conj_cone_tolerance                   3.
% 0.93/1.02  --extra_neg_conj                        none
% 0.93/1.02  --large_theory_mode                     true
% 0.93/1.02  --prolific_symb_bound                   200
% 0.93/1.02  --lt_threshold                          2000
% 0.93/1.02  --clause_weak_htbl                      true
% 0.93/1.02  --gc_record_bc_elim                     false
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing Options
% 0.93/1.02  
% 0.93/1.02  --preprocessing_flag                    true
% 0.93/1.02  --time_out_prep_mult                    0.1
% 0.93/1.02  --splitting_mode                        input
% 0.93/1.02  --splitting_grd                         true
% 0.93/1.02  --splitting_cvd                         false
% 0.93/1.02  --splitting_cvd_svl                     false
% 0.93/1.02  --splitting_nvd                         32
% 0.93/1.02  --sub_typing                            true
% 0.93/1.02  --prep_gs_sim                           true
% 0.93/1.02  --prep_unflatten                        true
% 0.93/1.02  --prep_res_sim                          true
% 0.93/1.02  --prep_upred                            true
% 0.93/1.02  --prep_sem_filter                       exhaustive
% 0.93/1.02  --prep_sem_filter_out                   false
% 0.93/1.02  --pred_elim                             true
% 0.93/1.02  --res_sim_input                         true
% 0.93/1.02  --eq_ax_congr_red                       true
% 0.93/1.02  --pure_diseq_elim                       true
% 0.93/1.02  --brand_transform                       false
% 0.93/1.02  --non_eq_to_eq                          false
% 0.93/1.02  --prep_def_merge                        true
% 0.93/1.02  --prep_def_merge_prop_impl              false
% 0.93/1.02  --prep_def_merge_mbd                    true
% 0.93/1.02  --prep_def_merge_tr_red                 false
% 0.93/1.02  --prep_def_merge_tr_cl                  false
% 0.93/1.02  --smt_preprocessing                     true
% 0.93/1.02  --smt_ac_axioms                         fast
% 0.93/1.02  --preprocessed_out                      false
% 0.93/1.02  --preprocessed_stats                    false
% 0.93/1.02  
% 0.93/1.02  ------ Abstraction refinement Options
% 0.93/1.02  
% 0.93/1.02  --abstr_ref                             []
% 0.93/1.02  --abstr_ref_prep                        false
% 0.93/1.02  --abstr_ref_until_sat                   false
% 0.93/1.02  --abstr_ref_sig_restrict                funpre
% 0.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.02  --abstr_ref_under                       []
% 0.93/1.02  
% 0.93/1.02  ------ SAT Options
% 0.93/1.02  
% 0.93/1.02  --sat_mode                              false
% 0.93/1.02  --sat_fm_restart_options                ""
% 0.93/1.02  --sat_gr_def                            false
% 0.93/1.02  --sat_epr_types                         true
% 0.93/1.02  --sat_non_cyclic_types                  false
% 0.93/1.02  --sat_finite_models                     false
% 0.93/1.02  --sat_fm_lemmas                         false
% 0.93/1.02  --sat_fm_prep                           false
% 0.93/1.02  --sat_fm_uc_incr                        true
% 0.93/1.02  --sat_out_model                         small
% 0.93/1.02  --sat_out_clauses                       false
% 0.93/1.02  
% 0.93/1.02  ------ QBF Options
% 0.93/1.02  
% 0.93/1.02  --qbf_mode                              false
% 0.93/1.02  --qbf_elim_univ                         false
% 0.93/1.02  --qbf_dom_inst                          none
% 0.93/1.02  --qbf_dom_pre_inst                      false
% 0.93/1.02  --qbf_sk_in                             false
% 0.93/1.02  --qbf_pred_elim                         true
% 0.93/1.02  --qbf_split                             512
% 0.93/1.02  
% 0.93/1.02  ------ BMC1 Options
% 0.93/1.02  
% 0.93/1.02  --bmc1_incremental                      false
% 0.93/1.02  --bmc1_axioms                           reachable_all
% 0.93/1.02  --bmc1_min_bound                        0
% 0.93/1.02  --bmc1_max_bound                        -1
% 0.93/1.02  --bmc1_max_bound_default                -1
% 0.93/1.02  --bmc1_symbol_reachability              true
% 0.93/1.02  --bmc1_property_lemmas                  false
% 0.93/1.02  --bmc1_k_induction                      false
% 0.93/1.02  --bmc1_non_equiv_states                 false
% 0.93/1.02  --bmc1_deadlock                         false
% 0.93/1.02  --bmc1_ucm                              false
% 0.93/1.02  --bmc1_add_unsat_core                   none
% 0.93/1.02  --bmc1_unsat_core_children              false
% 0.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.02  --bmc1_out_stat                         full
% 0.93/1.02  --bmc1_ground_init                      false
% 0.93/1.02  --bmc1_pre_inst_next_state              false
% 0.93/1.02  --bmc1_pre_inst_state                   false
% 0.93/1.02  --bmc1_pre_inst_reach_state             false
% 0.93/1.02  --bmc1_out_unsat_core                   false
% 0.93/1.02  --bmc1_aig_witness_out                  false
% 0.93/1.02  --bmc1_verbose                          false
% 0.93/1.02  --bmc1_dump_clauses_tptp                false
% 0.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.02  --bmc1_dump_file                        -
% 0.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.02  --bmc1_ucm_extend_mode                  1
% 0.93/1.02  --bmc1_ucm_init_mode                    2
% 0.93/1.02  --bmc1_ucm_cone_mode                    none
% 0.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.02  --bmc1_ucm_relax_model                  4
% 0.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.02  --bmc1_ucm_layered_model                none
% 0.93/1.02  --bmc1_ucm_max_lemma_size               10
% 0.93/1.02  
% 0.93/1.02  ------ AIG Options
% 0.93/1.02  
% 0.93/1.02  --aig_mode                              false
% 0.93/1.02  
% 0.93/1.02  ------ Instantiation Options
% 0.93/1.02  
% 0.93/1.02  --instantiation_flag                    true
% 0.93/1.02  --inst_sos_flag                         false
% 0.93/1.02  --inst_sos_phase                        true
% 0.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel_side                     none
% 0.93/1.02  --inst_solver_per_active                1400
% 0.93/1.02  --inst_solver_calls_frac                1.
% 0.93/1.02  --inst_passive_queue_type               priority_queues
% 0.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.02  --inst_passive_queues_freq              [25;2]
% 0.93/1.02  --inst_dismatching                      true
% 0.93/1.02  --inst_eager_unprocessed_to_passive     true
% 0.93/1.02  --inst_prop_sim_given                   true
% 0.93/1.02  --inst_prop_sim_new                     false
% 0.93/1.02  --inst_subs_new                         false
% 0.93/1.02  --inst_eq_res_simp                      false
% 0.93/1.02  --inst_subs_given                       false
% 0.93/1.02  --inst_orphan_elimination               true
% 0.93/1.02  --inst_learning_loop_flag               true
% 0.93/1.02  --inst_learning_start                   3000
% 0.93/1.02  --inst_learning_factor                  2
% 0.93/1.02  --inst_start_prop_sim_after_learn       3
% 0.93/1.02  --inst_sel_renew                        solver
% 0.93/1.02  --inst_lit_activity_flag                true
% 0.93/1.02  --inst_restr_to_given                   false
% 0.93/1.02  --inst_activity_threshold               500
% 0.93/1.02  --inst_out_proof                        true
% 0.93/1.02  
% 0.93/1.02  ------ Resolution Options
% 0.93/1.02  
% 0.93/1.02  --resolution_flag                       false
% 0.93/1.02  --res_lit_sel                           adaptive
% 0.93/1.02  --res_lit_sel_side                      none
% 0.93/1.02  --res_ordering                          kbo
% 0.93/1.02  --res_to_prop_solver                    active
% 0.93/1.02  --res_prop_simpl_new                    false
% 0.93/1.02  --res_prop_simpl_given                  true
% 0.93/1.02  --res_passive_queue_type                priority_queues
% 0.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.02  --res_passive_queues_freq               [15;5]
% 0.93/1.02  --res_forward_subs                      full
% 0.93/1.02  --res_backward_subs                     full
% 0.93/1.02  --res_forward_subs_resolution           true
% 0.93/1.02  --res_backward_subs_resolution          true
% 0.93/1.02  --res_orphan_elimination                true
% 0.93/1.02  --res_time_limit                        2.
% 0.93/1.02  --res_out_proof                         true
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Options
% 0.93/1.02  
% 0.93/1.02  --superposition_flag                    true
% 0.93/1.02  --sup_passive_queue_type                priority_queues
% 0.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.02  --demod_completeness_check              fast
% 0.93/1.02  --demod_use_ground                      true
% 0.93/1.02  --sup_to_prop_solver                    passive
% 0.93/1.02  --sup_prop_simpl_new                    true
% 0.93/1.02  --sup_prop_simpl_given                  true
% 0.93/1.02  --sup_fun_splitting                     false
% 0.93/1.02  --sup_smt_interval                      50000
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Simplification Setup
% 0.93/1.02  
% 0.93/1.02  --sup_indices_passive                   []
% 0.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_full_bw                           [BwDemod]
% 0.93/1.02  --sup_immed_triv                        [TrivRules]
% 0.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_immed_bw_main                     []
% 0.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  
% 0.93/1.02  ------ Combination Options
% 0.93/1.02  
% 0.93/1.02  --comb_res_mult                         3
% 0.93/1.02  --comb_sup_mult                         2
% 0.93/1.02  --comb_inst_mult                        10
% 0.93/1.02  
% 0.93/1.02  ------ Debug Options
% 0.93/1.02  
% 0.93/1.02  --dbg_backtrace                         false
% 0.93/1.02  --dbg_dump_prop_clauses                 false
% 0.93/1.02  --dbg_dump_prop_clauses_file            -
% 0.93/1.02  --dbg_out_stat                          false
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  ------ Proving...
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  % SZS status Theorem for theBenchmark.p
% 0.93/1.02  
% 0.93/1.02   Resolution empty clause
% 0.93/1.02  
% 0.93/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.93/1.02  
% 0.93/1.02  fof(f12,axiom,(
% 0.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.93/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f25,plain,(
% 0.93/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.02    inference(ennf_transformation,[],[f12])).
% 0.93/1.02  
% 0.93/1.02  fof(f26,plain,(
% 0.93/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.02    inference(flattening,[],[f25])).
% 0.93/1.02  
% 0.93/1.02  fof(f34,plain,(
% 0.93/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.02    inference(nnf_transformation,[],[f26])).
% 0.93/1.02  
% 0.93/1.02  fof(f53,plain,(
% 0.93/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.02    inference(cnf_transformation,[],[f34])).
% 0.93/1.02  
% 0.93/1.02  fof(f13,conjecture,(
% 0.93/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.93/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f14,negated_conjecture,(
% 0.93/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.93/1.02    inference(negated_conjecture,[],[f13])).
% 0.93/1.02  
% 0.93/1.02  fof(f27,plain,(
% 0.93/1.02    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.93/1.02    inference(ennf_transformation,[],[f14])).
% 0.93/1.02  
% 0.93/1.02  fof(f28,plain,(
% 0.93/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.93/1.02    inference(flattening,[],[f27])).
% 0.93/1.02  
% 0.93/1.02  fof(f36,plain,(
% 0.93/1.02    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 0.93/1.02    introduced(choice_axiom,[])).
% 0.93/1.02  
% 0.93/1.02  fof(f35,plain,(
% 0.93/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.93/1.02    introduced(choice_axiom,[])).
% 0.93/1.02  
% 0.93/1.02  fof(f37,plain,(
% 0.93/1.02    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.93/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36,f35])).
% 0.93/1.02  
% 0.93/1.02  fof(f63,plain,(
% 0.93/1.02    v1_funct_2(sK4,sK1,sK2)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f64,plain,(
% 0.93/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f10,axiom,(
% 0.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.93/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f22,plain,(
% 0.93/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.03    inference(ennf_transformation,[],[f10])).
% 0.93/1.03  
% 0.93/1.03  fof(f50,plain,(
% 0.93/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.03    inference(cnf_transformation,[],[f22])).
% 0.93/1.03  
% 0.93/1.03  fof(f60,plain,(
% 0.93/1.03    v1_funct_2(sK3,sK1,sK2)),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f61,plain,(
% 0.93/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f8,axiom,(
% 0.93/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f19,plain,(
% 0.93/1.03    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.93/1.03    inference(ennf_transformation,[],[f8])).
% 0.93/1.03  
% 0.93/1.03  fof(f20,plain,(
% 0.93/1.03    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.93/1.03    inference(flattening,[],[f19])).
% 0.93/1.03  
% 0.93/1.03  fof(f31,plain,(
% 0.93/1.03    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 0.93/1.03    introduced(choice_axiom,[])).
% 0.93/1.03  
% 0.93/1.03  fof(f32,plain,(
% 0.93/1.03    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).
% 0.93/1.03  
% 0.93/1.03  fof(f47,plain,(
% 0.93/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f32])).
% 0.93/1.03  
% 0.93/1.03  fof(f62,plain,(
% 0.93/1.03    v1_funct_1(sK4)),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f1,axiom,(
% 0.93/1.03    v1_xboole_0(k1_xboole_0)),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f38,plain,(
% 0.93/1.03    v1_xboole_0(k1_xboole_0)),
% 0.93/1.03    inference(cnf_transformation,[],[f1])).
% 0.93/1.03  
% 0.93/1.03  fof(f6,axiom,(
% 0.93/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f18,plain,(
% 0.93/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.93/1.03    inference(ennf_transformation,[],[f6])).
% 0.93/1.03  
% 0.93/1.03  fof(f45,plain,(
% 0.93/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f18])).
% 0.93/1.03  
% 0.93/1.03  fof(f9,axiom,(
% 0.93/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f21,plain,(
% 0.93/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.93/1.03    inference(ennf_transformation,[],[f9])).
% 0.93/1.03  
% 0.93/1.03  fof(f49,plain,(
% 0.93/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f21])).
% 0.93/1.03  
% 0.93/1.03  fof(f11,axiom,(
% 0.93/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f23,plain,(
% 0.93/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.93/1.03    inference(ennf_transformation,[],[f11])).
% 0.93/1.03  
% 0.93/1.03  fof(f24,plain,(
% 0.93/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.03    inference(flattening,[],[f23])).
% 0.93/1.03  
% 0.93/1.03  fof(f33,plain,(
% 0.93/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.03    inference(nnf_transformation,[],[f24])).
% 0.93/1.03  
% 0.93/1.03  fof(f52,plain,(
% 0.93/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.03    inference(cnf_transformation,[],[f33])).
% 0.93/1.03  
% 0.93/1.03  fof(f69,plain,(
% 0.93/1.03    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.03    inference(equality_resolution,[],[f52])).
% 0.93/1.03  
% 0.93/1.03  fof(f66,plain,(
% 0.93/1.03    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f2,axiom,(
% 0.93/1.03    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f15,plain,(
% 0.93/1.03    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.93/1.03    inference(ennf_transformation,[],[f2])).
% 0.93/1.03  
% 0.93/1.03  fof(f39,plain,(
% 0.93/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f15])).
% 0.93/1.03  
% 0.93/1.03  fof(f7,axiom,(
% 0.93/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.03  
% 0.93/1.03  fof(f46,plain,(
% 0.93/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.93/1.03    inference(cnf_transformation,[],[f7])).
% 0.93/1.03  
% 0.93/1.03  fof(f59,plain,(
% 0.93/1.03    v1_funct_1(sK3)),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f65,plain,(
% 0.93/1.03    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f37])).
% 0.93/1.03  
% 0.93/1.03  fof(f48,plain,(
% 0.93/1.03    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.93/1.03    inference(cnf_transformation,[],[f32])).
% 0.93/1.03  
% 0.93/1.03  cnf(c_20,plain,
% 0.93/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 0.93/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | k1_relset_1(X1,X2,X0) = X1
% 0.93/1.03      | k1_xboole_0 = X2 ),
% 0.93/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_24,negated_conjecture,
% 0.93/1.03      ( v1_funct_2(sK4,sK1,sK2) ),
% 0.93/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_449,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | k1_relset_1(X1,X2,X0) = X1
% 0.93/1.03      | sK4 != X0
% 0.93/1.03      | sK2 != X2
% 0.93/1.03      | sK1 != X1
% 0.93/1.03      | k1_xboole_0 = X2 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_450,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.93/1.03      | k1_relset_1(sK1,sK2,sK4) = sK1
% 0.93/1.03      | k1_xboole_0 = sK2 ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_449]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_23,negated_conjecture,
% 0.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 0.93/1.03      inference(cnf_transformation,[],[f64]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_452,plain,
% 0.93/1.03      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 0.93/1.03      inference(global_propositional_subsumption,[status(thm)],[c_450,c_23]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1058,plain,
% 0.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_12,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f50]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1060,plain,
% 0.93/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.93/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1446,plain,
% 0.93/1.03      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1058,c_1060]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1626,plain,
% 0.93/1.03      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_452,c_1446]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_27,negated_conjecture,
% 0.93/1.03      ( v1_funct_2(sK3,sK1,sK2) ),
% 0.93/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_460,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | k1_relset_1(X1,X2,X0) = X1
% 0.93/1.03      | sK3 != X0
% 0.93/1.03      | sK2 != X2
% 0.93/1.03      | sK1 != X1
% 0.93/1.03      | k1_xboole_0 = X2 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_461,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.93/1.03      | k1_relset_1(sK1,sK2,sK3) = sK1
% 0.93/1.03      | k1_xboole_0 = sK2 ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_460]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_26,negated_conjecture,
% 0.93/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 0.93/1.03      inference(cnf_transformation,[],[f61]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_463,plain,
% 0.93/1.03      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 0.93/1.03      inference(global_propositional_subsumption,[status(thm)],[c_461,c_26]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1056,plain,
% 0.93/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1447,plain,
% 0.93/1.03      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1056,c_1060]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1702,plain,
% 0.93/1.03      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_463,c_1447]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_10,plain,
% 0.93/1.03      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 0.93/1.03      | ~ v1_funct_1(X1)
% 0.93/1.03      | ~ v1_funct_1(X0)
% 0.93/1.03      | ~ v1_relat_1(X0)
% 0.93/1.03      | ~ v1_relat_1(X1)
% 0.93/1.03      | X0 = X1
% 0.93/1.03      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1062,plain,
% 0.93/1.03      ( X0 = X1
% 0.93/1.03      | k1_relat_1(X1) != k1_relat_1(X0)
% 0.93/1.03      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 0.93/1.03      | v1_funct_1(X1) != iProver_top
% 0.93/1.03      | v1_funct_1(X0) != iProver_top
% 0.93/1.03      | v1_relat_1(X0) != iProver_top
% 0.93/1.03      | v1_relat_1(X1) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2397,plain,
% 0.93/1.03      ( k1_relat_1(X0) != sK1
% 0.93/1.03      | sK4 = X0
% 0.93/1.03      | sK2 = k1_xboole_0
% 0.93/1.03      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 0.93/1.03      | v1_funct_1(X0) != iProver_top
% 0.93/1.03      | v1_funct_1(sK4) != iProver_top
% 0.93/1.03      | v1_relat_1(X0) != iProver_top
% 0.93/1.03      | v1_relat_1(sK4) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1626,c_1062]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_25,negated_conjecture,
% 0.93/1.03      ( v1_funct_1(sK4) ),
% 0.93/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_32,plain,
% 0.93/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_34,plain,
% 0.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_0,plain,
% 0.93/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f38]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_88,plain,
% 0.93/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_696,plain,
% 0.93/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.93/1.03      theory(equality) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1428,plain,
% 0.93/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_696]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1429,plain,
% 0.93/1.03      ( sK2 != X0
% 0.93/1.03      | v1_xboole_0(X0) != iProver_top
% 0.93/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1431,plain,
% 0.93/1.03      ( sK2 != k1_xboole_0
% 0.93/1.03      | v1_xboole_0(sK2) = iProver_top
% 0.93/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_1429]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_7,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1643,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 0.93/1.03      | ~ v1_relat_1(X0)
% 0.93/1.03      | v1_relat_1(sK4) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2081,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.93/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 0.93/1.03      | v1_relat_1(sK4) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_1643]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2082,plain,
% 0.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 0.93/1.03      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 0.93/1.03      | v1_relat_1(sK4) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_11,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | ~ v1_xboole_0(X2)
% 0.93/1.03      | v1_xboole_0(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1061,plain,
% 0.93/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.93/1.03      | v1_xboole_0(X2) != iProver_top
% 0.93/1.03      | v1_xboole_0(X0) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1932,plain,
% 0.93/1.03      ( v1_xboole_0(sK4) = iProver_top | v1_xboole_0(sK2) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1058,c_1061]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_13,plain,
% 0.93/1.03      ( r2_relset_1(X0,X1,X2,X2)
% 0.93/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.93/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_21,negated_conjecture,
% 0.93/1.03      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 0.93/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_290,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.03      | sK4 != X0
% 0.93/1.03      | sK3 != X0
% 0.93/1.03      | sK2 != X2
% 0.93/1.03      | sK1 != X1 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_291,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | sK3 != sK4 ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_290]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1,plain,
% 0.93/1.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 0.93/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1242,plain,
% 0.93/1.03      ( ~ v1_xboole_0(sK4) | ~ v1_xboole_0(sK3) | sK3 = sK4 ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1243,plain,
% 0.93/1.03      ( sK3 = sK4
% 0.93/1.03      | v1_xboole_0(sK4) != iProver_top
% 0.93/1.03      | v1_xboole_0(sK3) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1933,plain,
% 0.93/1.03      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK2) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1056,c_1061]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2168,plain,
% 0.93/1.03      ( v1_xboole_0(sK2) != iProver_top ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_1932,c_23,c_291,c_1243,c_1933]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_8,plain,
% 0.93/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.93/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2533,plain,
% 0.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2534,plain,
% 0.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2835,plain,
% 0.93/1.03      ( v1_relat_1(X0) != iProver_top
% 0.93/1.03      | sK4 = X0
% 0.93/1.03      | k1_relat_1(X0) != sK1
% 0.93/1.03      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 0.93/1.03      | v1_funct_1(X0) != iProver_top ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_2397,c_32,c_23,c_34,c_88,c_291,c_1243,c_1431,c_1932,
% 0.93/1.03                 c_1933,c_2082,c_2534]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2836,plain,
% 0.93/1.03      ( k1_relat_1(X0) != sK1
% 0.93/1.03      | sK4 = X0
% 0.93/1.03      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 0.93/1.03      | v1_funct_1(X0) != iProver_top
% 0.93/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.93/1.03      inference(renaming,[status(thm)],[c_2835]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2847,plain,
% 0.93/1.03      ( sK4 = sK3
% 0.93/1.03      | sK2 = k1_xboole_0
% 0.93/1.03      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 0.93/1.03      | v1_funct_1(sK3) != iProver_top
% 0.93/1.03      | v1_relat_1(sK3) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1702,c_2836]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_28,negated_conjecture,
% 0.93/1.03      ( v1_funct_1(sK3) ),
% 0.93/1.03      inference(cnf_transformation,[],[f59]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_29,plain,
% 0.93/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_31,plain,
% 0.93/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1638,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 0.93/1.03      | ~ v1_relat_1(X0)
% 0.93/1.03      | v1_relat_1(sK3) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2073,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.93/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 0.93/1.03      | v1_relat_1(sK3) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_1638]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2074,plain,
% 0.93/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 0.93/1.03      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 0.93/1.03      | v1_relat_1(sK3) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2073]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2860,plain,
% 0.93/1.03      ( sK4 = sK3 | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_2847,c_29,c_31,c_23,c_88,c_291,c_1243,c_1431,c_1932,
% 0.93/1.03                 c_1933,c_2074,c_2534]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2866,plain,
% 0.93/1.03      ( sK4 = sK3
% 0.93/1.03      | sK2 = k1_xboole_0
% 0.93/1.03      | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1702,c_2860]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2923,plain,
% 0.93/1.03      ( sK4 = sK3 | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_2866,c_23,c_88,c_291,c_1243,c_1431,c_1932,c_1933]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_22,negated_conjecture,
% 0.93/1.03      ( ~ r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f65]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1059,plain,
% 0.93/1.03      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 0.93/1.03      | r2_hidden(X0,sK1) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2929,plain,
% 0.93/1.03      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 0.93/1.03      | sK4 = sK3 ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_2923,c_1059]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_9,plain,
% 0.93/1.03      ( ~ v1_funct_1(X0)
% 0.93/1.03      | ~ v1_funct_1(X1)
% 0.93/1.03      | ~ v1_relat_1(X1)
% 0.93/1.03      | ~ v1_relat_1(X0)
% 0.93/1.03      | X1 = X0
% 0.93/1.03      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 0.93/1.03      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 0.93/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1063,plain,
% 0.93/1.03      ( X0 = X1
% 0.93/1.03      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 0.93/1.03      | k1_relat_1(X1) != k1_relat_1(X0)
% 0.93/1.03      | v1_funct_1(X0) != iProver_top
% 0.93/1.03      | v1_funct_1(X1) != iProver_top
% 0.93/1.03      | v1_relat_1(X1) != iProver_top
% 0.93/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2932,plain,
% 0.93/1.03      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 0.93/1.03      | sK4 = sK3
% 0.93/1.03      | v1_funct_1(sK4) != iProver_top
% 0.93/1.03      | v1_funct_1(sK3) != iProver_top
% 0.93/1.03      | v1_relat_1(sK4) != iProver_top
% 0.93/1.03      | v1_relat_1(sK3) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_2929,c_1063]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2933,plain,
% 0.93/1.03      ( ~ v1_funct_1(sK4)
% 0.93/1.03      | ~ v1_funct_1(sK3)
% 0.93/1.03      | ~ v1_relat_1(sK4)
% 0.93/1.03      | ~ v1_relat_1(sK3)
% 0.93/1.03      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 0.93/1.03      | sK4 = sK3 ),
% 0.93/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2932]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3053,plain,
% 0.93/1.03      ( k1_relat_1(sK3) != k1_relat_1(sK4) | sK4 = sK3 ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_2932,c_28,c_26,c_25,c_23,c_2073,c_2081,c_2533,c_2933]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3057,plain,
% 0.93/1.03      ( k1_relat_1(sK3) != sK1 | sK4 = sK3 | sK2 = k1_xboole_0 ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_1626,c_3053]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3133,plain,
% 0.93/1.03      ( sK4 = sK3 ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_3057,c_23,c_88,c_291,c_1243,c_1431,c_1702,c_1932,c_1933]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_293,plain,
% 0.93/1.03      ( sK3 != sK4 ),
% 0.93/1.03      inference(global_propositional_subsumption,[status(thm)],[c_291,c_23]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3150,plain,
% 0.93/1.03      ( sK3 != sK3 ),
% 0.93/1.03      inference(demodulation,[status(thm)],[c_3133,c_293]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3151,plain,
% 0.93/1.03      ( $false ),
% 0.93/1.03      inference(equality_resolution_simp,[status(thm)],[c_3150]) ).
% 0.93/1.03  
% 0.93/1.03  
% 0.93/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.93/1.03  
% 0.93/1.03  ------                               Statistics
% 0.93/1.03  
% 0.93/1.03  ------ General
% 0.93/1.03  
% 0.93/1.03  abstr_ref_over_cycles:                  0
% 0.93/1.03  abstr_ref_under_cycles:                 0
% 0.93/1.03  gc_basic_clause_elim:                   0
% 0.93/1.03  forced_gc_time:                         0
% 0.93/1.03  parsing_time:                           0.017
% 0.93/1.03  unif_index_cands_time:                  0.
% 0.93/1.03  unif_index_add_time:                    0.
% 0.93/1.03  orderings_time:                         0.
% 0.93/1.03  out_proof_time:                         0.009
% 0.93/1.03  total_time:                             0.146
% 0.93/1.03  num_of_symbols:                         49
% 0.93/1.03  num_of_terms:                           2676
% 0.93/1.03  
% 0.93/1.03  ------ Preprocessing
% 0.93/1.03  
% 0.93/1.03  num_of_splits:                          0
% 0.93/1.03  num_of_split_atoms:                     0
% 0.93/1.03  num_of_reused_defs:                     0
% 0.93/1.03  num_eq_ax_congr_red:                    11
% 0.93/1.03  num_of_sem_filtered_clauses:            1
% 0.93/1.03  num_of_subtypes:                        0
% 0.93/1.03  monotx_restored_types:                  0
% 0.93/1.03  sat_num_of_epr_types:                   0
% 0.93/1.03  sat_num_of_non_cyclic_types:            0
% 0.93/1.03  sat_guarded_non_collapsed_types:        0
% 0.93/1.03  num_pure_diseq_elim:                    0
% 0.93/1.03  simp_replaced_by:                       0
% 0.93/1.03  res_preprocessed:                       127
% 0.93/1.03  prep_upred:                             0
% 0.93/1.03  prep_unflattend:                        47
% 0.93/1.03  smt_new_axioms:                         0
% 0.93/1.03  pred_elim_cands:                        5
% 0.93/1.03  pred_elim:                              2
% 0.93/1.03  pred_elim_cl:                           4
% 0.93/1.03  pred_elim_cycles:                       5
% 0.93/1.03  merged_defs:                            0
% 0.93/1.03  merged_defs_ncl:                        0
% 0.93/1.03  bin_hyper_res:                          0
% 0.93/1.03  prep_cycles:                            4
% 0.93/1.03  pred_elim_time:                         0.009
% 0.93/1.03  splitting_time:                         0.
% 0.93/1.03  sem_filter_time:                        0.
% 0.93/1.03  monotx_time:                            0.001
% 0.93/1.03  subtype_inf_time:                       0.
% 0.93/1.03  
% 0.93/1.03  ------ Problem properties
% 0.93/1.03  
% 0.93/1.03  clauses:                                25
% 0.93/1.03  conjectures:                            5
% 0.93/1.03  epr:                                    5
% 0.93/1.03  horn:                                   19
% 0.93/1.03  ground:                                 12
% 0.93/1.03  unary:                                  10
% 0.93/1.03  binary:                                 4
% 0.93/1.03  lits:                                   61
% 0.93/1.03  lits_eq:                                28
% 0.93/1.03  fd_pure:                                0
% 0.93/1.03  fd_pseudo:                              0
% 0.93/1.03  fd_cond:                                1
% 0.93/1.03  fd_pseudo_cond:                         3
% 0.93/1.03  ac_symbols:                             0
% 0.93/1.03  
% 0.93/1.03  ------ Propositional Solver
% 0.93/1.03  
% 0.93/1.03  prop_solver_calls:                      27
% 0.93/1.03  prop_fast_solver_calls:                 864
% 0.93/1.03  smt_solver_calls:                       0
% 0.93/1.03  smt_fast_solver_calls:                  0
% 0.93/1.03  prop_num_of_clauses:                    979
% 0.93/1.03  prop_preprocess_simplified:             3971
% 0.93/1.03  prop_fo_subsumed:                       26
% 0.93/1.03  prop_solver_time:                       0.
% 0.93/1.03  smt_solver_time:                        0.
% 0.93/1.03  smt_fast_solver_time:                   0.
% 0.93/1.03  prop_fast_solver_time:                  0.
% 0.93/1.03  prop_unsat_core_time:                   0.
% 0.93/1.03  
% 0.93/1.03  ------ QBF
% 0.93/1.03  
% 0.93/1.03  qbf_q_res:                              0
% 0.93/1.03  qbf_num_tautologies:                    0
% 0.93/1.03  qbf_prep_cycles:                        0
% 0.93/1.03  
% 0.93/1.03  ------ BMC1
% 0.93/1.03  
% 0.93/1.03  bmc1_current_bound:                     -1
% 0.93/1.03  bmc1_last_solved_bound:                 -1
% 0.93/1.03  bmc1_unsat_core_size:                   -1
% 0.93/1.03  bmc1_unsat_core_parents_size:           -1
% 0.93/1.03  bmc1_merge_next_fun:                    0
% 0.93/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.93/1.03  
% 0.93/1.03  ------ Instantiation
% 0.93/1.03  
% 0.93/1.03  inst_num_of_clauses:                    352
% 0.93/1.03  inst_num_in_passive:                    105
% 0.93/1.03  inst_num_in_active:                     213
% 0.93/1.03  inst_num_in_unprocessed:                34
% 0.93/1.03  inst_num_of_loops:                      250
% 0.93/1.03  inst_num_of_learning_restarts:          0
% 0.93/1.03  inst_num_moves_active_passive:          34
% 0.93/1.03  inst_lit_activity:                      0
% 0.93/1.03  inst_lit_activity_moves:                0
% 0.93/1.03  inst_num_tautologies:                   0
% 0.93/1.03  inst_num_prop_implied:                  0
% 0.93/1.03  inst_num_existing_simplified:           0
% 0.93/1.03  inst_num_eq_res_simplified:             0
% 0.93/1.03  inst_num_child_elim:                    0
% 0.93/1.03  inst_num_of_dismatching_blockings:      93
% 0.93/1.03  inst_num_of_non_proper_insts:           418
% 0.93/1.03  inst_num_of_duplicates:                 0
% 0.93/1.03  inst_inst_num_from_inst_to_res:         0
% 0.93/1.03  inst_dismatching_checking_time:         0.
% 0.93/1.03  
% 0.93/1.03  ------ Resolution
% 0.93/1.03  
% 0.93/1.03  res_num_of_clauses:                     0
% 0.93/1.03  res_num_in_passive:                     0
% 0.93/1.03  res_num_in_active:                      0
% 0.93/1.03  res_num_of_loops:                       131
% 0.93/1.03  res_forward_subset_subsumed:            24
% 0.93/1.03  res_backward_subset_subsumed:           0
% 0.93/1.03  res_forward_subsumed:                   0
% 0.93/1.03  res_backward_subsumed:                  0
% 0.93/1.03  res_forward_subsumption_resolution:     0
% 0.93/1.03  res_backward_subsumption_resolution:    0
% 0.93/1.03  res_clause_to_clause_subsumption:       72
% 0.93/1.03  res_orphan_elimination:                 0
% 0.93/1.03  res_tautology_del:                      34
% 0.93/1.03  res_num_eq_res_simplified:              0
% 0.93/1.03  res_num_sel_changes:                    0
% 0.93/1.03  res_moves_from_active_to_pass:          0
% 0.93/1.03  
% 0.93/1.03  ------ Superposition
% 0.93/1.03  
% 0.93/1.03  sup_time_total:                         0.
% 0.93/1.03  sup_time_generating:                    0.
% 0.93/1.03  sup_time_sim_full:                      0.
% 0.93/1.03  sup_time_sim_immed:                     0.
% 0.93/1.03  
% 0.93/1.03  sup_num_of_clauses:                     36
% 0.93/1.03  sup_num_in_active:                      31
% 0.93/1.03  sup_num_in_passive:                     5
% 0.93/1.03  sup_num_of_loops:                       48
% 0.93/1.03  sup_fw_superposition:                   35
% 0.93/1.03  sup_bw_superposition:                   8
% 0.93/1.03  sup_immediate_simplified:               5
% 0.93/1.03  sup_given_eliminated:                   0
% 0.93/1.03  comparisons_done:                       0
% 0.93/1.03  comparisons_avoided:                    9
% 0.93/1.03  
% 0.93/1.03  ------ Simplifications
% 0.93/1.03  
% 0.93/1.03  
% 0.93/1.03  sim_fw_subset_subsumed:                 2
% 0.93/1.03  sim_bw_subset_subsumed:                 4
% 0.93/1.03  sim_fw_subsumed:                        3
% 0.93/1.03  sim_bw_subsumed:                        0
% 0.93/1.03  sim_fw_subsumption_res:                 0
% 0.93/1.03  sim_bw_subsumption_res:                 0
% 0.93/1.03  sim_tautology_del:                      0
% 0.93/1.03  sim_eq_tautology_del:                   7
% 0.93/1.03  sim_eq_res_simp:                        0
% 0.93/1.03  sim_fw_demodulated:                     4
% 0.93/1.03  sim_bw_demodulated:                     15
% 0.93/1.03  sim_light_normalised:                   0
% 0.93/1.03  sim_joinable_taut:                      0
% 0.93/1.03  sim_joinable_simp:                      0
% 0.93/1.03  sim_ac_normalised:                      0
% 0.93/1.03  sim_smt_subsumption:                    0
% 0.93/1.03  
%------------------------------------------------------------------------------
