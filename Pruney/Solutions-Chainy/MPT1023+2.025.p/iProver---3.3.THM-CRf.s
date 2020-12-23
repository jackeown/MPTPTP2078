%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:45 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  181 (2062 expanded)
%              Number of clauses        :  112 ( 640 expanded)
%              Number of leaves         :   20 ( 523 expanded)
%              Depth                    :   21
%              Number of atoms          :  687 (13195 expanded)
%              Number of equality atoms :  306 (3103 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK8)
        & ! [X4] :
            ( k1_funct_1(sK8,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK8,X0,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK5,sK6,sK7,X3)
          & ! [X4] :
              ( k1_funct_1(sK7,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
    & ! [X4] :
        ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f40,f63,f62])).

fof(f105,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f64])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f52])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f108,plain,(
    ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
            | ~ r2_hidden(k4_tarski(X4,X5),X2) )
          & ( r2_hidden(k4_tarski(X4,X5),X3)
            | r2_hidden(k4_tarski(X4,X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK4(X0,X1,X2,X3),X1)
                & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK8 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_39])).

cnf(c_678,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_680,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_38])).

cnf(c_2861,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2866,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4458,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2861,c_2866])).

cnf(c_4732,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_680,c_4458])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_42])).

cnf(c_689,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_691,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_41])).

cnf(c_2859,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4459,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2859,c_2866])).

cnf(c_4735,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_691,c_4459])).

cnf(c_18,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2875,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9368,plain,
    ( k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_2875])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_44,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3273,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3274,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_14596,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9368,c_44,c_46,c_3274])).

cnf(c_14597,plain,
    ( k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14596])).

cnf(c_14608,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(sK8,sK7),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4732,c_14597])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_47,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_49,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3270,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3271,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3270])).

cnf(c_28,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3336,plain,
    ( r2_relset_1(sK5,sK6,sK7,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3502,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1961,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3633,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_3793,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_1970,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_3501,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(sK5,sK6,sK7,sK7)
    | X2 != sK7
    | X3 != sK7
    | X1 != sK6
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_4048,plain,
    ( r2_relset_1(sK5,sK6,sK7,sK8)
    | ~ r2_relset_1(sK5,sK6,sK7,sK7)
    | sK8 != sK7
    | sK7 != sK7
    | sK6 != sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3501])).

cnf(c_14738,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK8,sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14608,c_41,c_47,c_49,c_36,c_3271,c_3336,c_3502,c_3633,c_3793,c_4048])).

cnf(c_14744,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK8,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4732,c_14738])).

cnf(c_1962,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3286,plain,
    ( sK6 != X0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_3632,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_5495,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1962,c_1961])).

cnf(c_15073,plain,
    ( sK5 = k1_relset_1(sK5,sK6,sK8)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[status(thm)],[c_5495,c_680])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_117,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_118,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9520,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_9521,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9520])).

cnf(c_4384,plain,
    ( k1_relat_1(sK8) != X0
    | k1_relat_1(sK8) = k1_relat_1(sK7)
    | k1_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_12709,plain,
    ( k1_relat_1(sK8) = k1_relat_1(sK7)
    | k1_relat_1(sK8) != sK5
    | k1_relat_1(sK7) != sK5 ),
    inference(instantiation,[status(thm)],[c_4384])).

cnf(c_9367,plain,
    ( k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4732,c_2875])).

cnf(c_13250,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9367,c_47,c_49,c_3271])).

cnf(c_13251,plain,
    ( k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13250])).

cnf(c_13263,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK2(sK7,sK8),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_13251])).

cnf(c_14347,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13263,c_44,c_41,c_46,c_36,c_3274,c_3336,c_3502,c_3633,c_3793,c_4048])).

cnf(c_14353,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK7,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_14347])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2880,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14584,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK2(sK7,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_14353,c_2880])).

cnf(c_37,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_15060,plain,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK8,X0) = k1_funct_1(sK7,X0) ),
    inference(resolution,[status(thm)],[c_5495,c_37])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15294,plain,
    ( ~ m1_subset_1(sK2(sK7,sK8),sK5)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_relat_1(sK8) != k1_relat_1(sK7)
    | sK8 = sK7 ),
    inference(resolution,[status(thm)],[c_15060,c_17])).

cnf(c_15295,plain,
    ( k1_relat_1(sK8) != k1_relat_1(sK7)
    | sK8 = sK7
    | m1_subset_1(sK2(sK7,sK8),sK5) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15294])).

cnf(c_15333,plain,
    ( k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15073,c_44,c_41,c_46,c_47,c_49,c_36,c_117,c_118,c_3271,c_3274,c_3336,c_3502,c_3633,c_3793,c_4048,c_4732,c_4735,c_9521,c_12709,c_14584,c_15295])).

cnf(c_15652,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14744,c_44,c_41,c_46,c_47,c_49,c_36,c_3271,c_3274,c_3336,c_3502,c_3633,c_3793,c_4048,c_4732,c_4735,c_12709,c_14584,c_15295])).

cnf(c_15716,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15652,c_2861])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_15722,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15716,c_8])).

cnf(c_15717,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15652,c_2859])).

cnf(c_15719,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15717,c_8])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_14508,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r1_tarski(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_14509,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14508])).

cnf(c_14511,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14509])).

cnf(c_7359,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7360,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7359])).

cnf(c_7362,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7360])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_314])).

cnf(c_398,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_315])).

cnf(c_3616,plain,
    ( ~ r1_tarski(sK7,X0)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,X1,sK7),sK4(sK5,sK6,X1,sK7)),sK7)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_5436,plain,
    ( ~ r1_tarski(sK7,X0)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_3616])).

cnf(c_5437,plain,
    ( r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5436])).

cnf(c_5439,plain,
    ( r1_tarski(sK7,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5437])).

cnf(c_4349,plain,
    ( ~ r1_tarski(sK8,X0)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_4350,plain,
    ( r1_tarski(sK8,X0) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4349])).

cnf(c_4352,plain,
    ( r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_22,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3395,plain,
    ( r2_relset_1(sK5,sK6,X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(k4_tarski(sK3(sK5,sK6,X0,sK7),sK4(sK5,sK6,X0,sK7)),X0)
    | r2_hidden(k4_tarski(sK3(sK5,sK6,X0,sK7),sK4(sK5,sK6,X0,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3886,plain,
    ( r2_relset_1(sK5,sK6,sK8,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8)
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_3887,plain,
    ( r2_relset_1(sK5,sK6,sK8,sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3886])).

cnf(c_2864,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3405,plain,
    ( sK8 = X0
    | r2_relset_1(sK5,sK6,sK8,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2861,c_2864])).

cnf(c_3641,plain,
    ( sK8 = sK7
    | r2_relset_1(sK5,sK6,sK8,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_3405])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15722,c_15719,c_14511,c_7362,c_5439,c_4352,c_4048,c_3887,c_3793,c_3641,c_3633,c_3502,c_3336,c_123,c_36,c_49,c_46,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.06/0.99  
% 4.06/0.99  ------  iProver source info
% 4.06/0.99  
% 4.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.06/0.99  git: non_committed_changes: false
% 4.06/0.99  git: last_make_outside_of_git: false
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  ------ Parsing...
% 4.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.06/0.99  
% 4.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.06/0.99  ------ Proving...
% 4.06/0.99  ------ Problem Properties 
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  clauses                                 42
% 4.06/0.99  conjectures                             6
% 4.06/0.99  EPR                                     11
% 4.06/0.99  Horn                                    31
% 4.06/0.99  unary                                   9
% 4.06/0.99  binary                                  15
% 4.06/0.99  lits                                    118
% 4.06/0.99  lits eq                                 28
% 4.06/0.99  fd_pure                                 0
% 4.06/0.99  fd_pseudo                               0
% 4.06/0.99  fd_cond                                 2
% 4.06/0.99  fd_pseudo_cond                          3
% 4.06/0.99  AC symbols                              0
% 4.06/0.99  
% 4.06/0.99  ------ Input Options Time Limit: Unbounded
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ 
% 4.06/0.99  Current options:
% 4.06/0.99  ------ 
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  ------ Proving...
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS status Theorem for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  fof(f18,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f37,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f18])).
% 4.06/0.99  
% 4.06/0.99  fof(f38,plain,(
% 4.06/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(flattening,[],[f37])).
% 4.06/0.99  
% 4.06/0.99  fof(f61,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(nnf_transformation,[],[f38])).
% 4.06/0.99  
% 4.06/0.99  fof(f95,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f61])).
% 4.06/0.99  
% 4.06/0.99  fof(f19,conjecture,(
% 4.06/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f20,negated_conjecture,(
% 4.06/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 4.06/0.99    inference(negated_conjecture,[],[f19])).
% 4.06/0.99  
% 4.06/0.99  fof(f39,plain,(
% 4.06/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.06/0.99    inference(ennf_transformation,[],[f20])).
% 4.06/0.99  
% 4.06/0.99  fof(f40,plain,(
% 4.06/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.06/0.99    inference(flattening,[],[f39])).
% 4.06/0.99  
% 4.06/0.99  fof(f63,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK8) & ! [X4] : (k1_funct_1(sK8,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK8,X0,X1) & v1_funct_1(sK8))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f62,plain,(
% 4.06/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f64,plain,(
% 4.06/0.99    (~r2_relset_1(sK5,sK6,sK7,sK8) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f40,f63,f62])).
% 4.06/0.99  
% 4.06/0.99  fof(f105,plain,(
% 4.06/0.99    v1_funct_2(sK8,sK5,sK6)),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f106,plain,(
% 4.06/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f16,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f34,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f16])).
% 4.06/0.99  
% 4.06/0.99  fof(f92,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f34])).
% 4.06/0.99  
% 4.06/0.99  fof(f102,plain,(
% 4.06/0.99    v1_funct_2(sK7,sK5,sK6)),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f103,plain,(
% 4.06/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f12,axiom,(
% 4.06/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f29,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.06/0.99    inference(ennf_transformation,[],[f12])).
% 4.06/0.99  
% 4.06/0.99  fof(f30,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.06/0.99    inference(flattening,[],[f29])).
% 4.06/0.99  
% 4.06/0.99  fof(f52,plain,(
% 4.06/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f53,plain,(
% 4.06/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f52])).
% 4.06/0.99  
% 4.06/0.99  fof(f82,plain,(
% 4.06/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f53])).
% 4.06/0.99  
% 4.06/0.99  fof(f101,plain,(
% 4.06/0.99    v1_funct_1(sK7)),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f14,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f32,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f14])).
% 4.06/0.99  
% 4.06/0.99  fof(f85,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f32])).
% 4.06/0.99  
% 4.06/0.99  fof(f104,plain,(
% 4.06/0.99    v1_funct_1(sK8)),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f108,plain,(
% 4.06/0.99    ~r2_relset_1(sK5,sK6,sK7,sK8)),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f17,axiom,(
% 4.06/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f35,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.06/0.99    inference(ennf_transformation,[],[f17])).
% 4.06/0.99  
% 4.06/0.99  fof(f36,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(flattening,[],[f35])).
% 4.06/0.99  
% 4.06/0.99  fof(f60,plain,(
% 4.06/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(nnf_transformation,[],[f36])).
% 4.06/0.99  
% 4.06/0.99  fof(f94,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f60])).
% 4.06/0.99  
% 4.06/0.99  fof(f111,plain,(
% 4.06/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(equality_resolution,[],[f94])).
% 4.06/0.99  
% 4.06/0.99  fof(f93,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f60])).
% 4.06/0.99  
% 4.06/0.99  fof(f6,axiom,(
% 4.06/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f49,plain,(
% 4.06/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.06/0.99    inference(nnf_transformation,[],[f6])).
% 4.06/0.99  
% 4.06/0.99  fof(f50,plain,(
% 4.06/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.06/0.99    inference(flattening,[],[f49])).
% 4.06/0.99  
% 4.06/0.99  fof(f73,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f50])).
% 4.06/0.99  
% 4.06/0.99  fof(f74,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.06/0.99    inference(cnf_transformation,[],[f50])).
% 4.06/0.99  
% 4.06/0.99  fof(f110,plain,(
% 4.06/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.06/0.99    inference(equality_resolution,[],[f74])).
% 4.06/0.99  
% 4.06/0.99  fof(f8,axiom,(
% 4.06/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f25,plain,(
% 4.06/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f8])).
% 4.06/0.99  
% 4.06/0.99  fof(f77,plain,(
% 4.06/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f25])).
% 4.06/0.99  
% 4.06/0.99  fof(f107,plain,(
% 4.06/0.99    ( ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~m1_subset_1(X4,sK5)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f64])).
% 4.06/0.99  
% 4.06/0.99  fof(f83,plain,(
% 4.06/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f53])).
% 4.06/0.99  
% 4.06/0.99  fof(f75,plain,(
% 4.06/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.06/0.99    inference(cnf_transformation,[],[f50])).
% 4.06/0.99  
% 4.06/0.99  fof(f109,plain,(
% 4.06/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.06/0.99    inference(equality_resolution,[],[f75])).
% 4.06/0.99  
% 4.06/0.99  fof(f9,axiom,(
% 4.06/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f51,plain,(
% 4.06/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.06/0.99    inference(nnf_transformation,[],[f9])).
% 4.06/0.99  
% 4.06/0.99  fof(f78,plain,(
% 4.06/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f51])).
% 4.06/0.99  
% 4.06/0.99  fof(f11,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f28,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.06/0.99    inference(ennf_transformation,[],[f11])).
% 4.06/0.99  
% 4.06/0.99  fof(f81,plain,(
% 4.06/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f28])).
% 4.06/0.99  
% 4.06/0.99  fof(f79,plain,(
% 4.06/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.06/0.99    inference(cnf_transformation,[],[f51])).
% 4.06/0.99  
% 4.06/0.99  fof(f15,axiom,(
% 4.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f33,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(ennf_transformation,[],[f15])).
% 4.06/0.99  
% 4.06/0.99  fof(f54,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(nnf_transformation,[],[f33])).
% 4.06/0.99  
% 4.06/0.99  fof(f55,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(flattening,[],[f54])).
% 4.06/0.99  
% 4.06/0.99  fof(f56,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(rectify,[],[f55])).
% 4.06/0.99  
% 4.06/0.99  fof(f58,plain,(
% 4.06/0.99    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)))) )),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f57,plain,(
% 4.06/0.99    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0)))),
% 4.06/0.99    introduced(choice_axiom,[])).
% 4.06/0.99  
% 4.06/0.99  fof(f59,plain,(
% 4.06/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).
% 4.06/0.99  
% 4.06/0.99  fof(f90,plain,(
% 4.06/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.06/0.99    inference(cnf_transformation,[],[f59])).
% 4.06/0.99  
% 4.06/0.99  fof(f3,axiom,(
% 4.06/0.99    v1_xboole_0(k1_xboole_0)),
% 4.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.06/0.99  
% 4.06/0.99  fof(f70,plain,(
% 4.06/0.99    v1_xboole_0(k1_xboole_0)),
% 4.06/0.99    inference(cnf_transformation,[],[f3])).
% 4.06/0.99  
% 4.06/0.99  cnf(c_35,plain,
% 4.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.06/0.99      | k1_xboole_0 = X2 ),
% 4.06/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_39,negated_conjecture,
% 4.06/0.99      ( v1_funct_2(sK8,sK5,sK6) ),
% 4.06/0.99      inference(cnf_transformation,[],[f105]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_677,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.06/0.99      | sK8 != X0
% 4.06/0.99      | sK6 != X2
% 4.06/0.99      | sK5 != X1
% 4.06/0.99      | k1_xboole_0 = X2 ),
% 4.06/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_39]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_678,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | k1_relset_1(sK5,sK6,sK8) = sK5
% 4.06/0.99      | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(unflattening,[status(thm)],[c_677]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_38,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f106]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_680,plain,
% 4.06/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5 | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_678,c_38]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2861,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_27,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2866,plain,
% 4.06/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4458,plain,
% 4.06/0.99      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2861,c_2866]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4732,plain,
% 4.06/0.99      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_680,c_4458]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_42,negated_conjecture,
% 4.06/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 4.06/0.99      inference(cnf_transformation,[],[f102]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_688,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.06/0.99      | sK7 != X0
% 4.06/0.99      | sK6 != X2
% 4.06/0.99      | sK5 != X1
% 4.06/0.99      | k1_xboole_0 = X2 ),
% 4.06/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_42]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_689,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | k1_relset_1(sK5,sK6,sK7) = sK5
% 4.06/0.99      | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(unflattening,[status(thm)],[c_688]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_41,negated_conjecture,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f103]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_691,plain,
% 4.06/0.99      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_689,c_41]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2859,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4459,plain,
% 4.06/0.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2859,c_2866]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4735,plain,
% 4.06/0.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_691,c_4459]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_18,plain,
% 4.06/0.99      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 4.06/0.99      | ~ v1_relat_1(X1)
% 4.06/0.99      | ~ v1_relat_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X1)
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | X1 = X0
% 4.06/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2875,plain,
% 4.06/0.99      ( X0 = X1
% 4.06/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 4.06/0.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 4.06/0.99      | v1_relat_1(X1) != iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9368,plain,
% 4.06/0.99      ( k1_relat_1(X0) != sK5
% 4.06/0.99      | sK7 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top
% 4.06/0.99      | v1_relat_1(sK7) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(sK7) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4735,c_2875]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_43,negated_conjecture,
% 4.06/0.99      ( v1_funct_1(sK7) ),
% 4.06/0.99      inference(cnf_transformation,[],[f101]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_44,plain,
% 4.06/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_46,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_20,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.06/0.99      | v1_relat_1(X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3273,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | v1_relat_1(sK7) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3274,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 4.06/0.99      | v1_relat_1(sK7) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14596,plain,
% 4.06/0.99      ( v1_funct_1(X0) != iProver_top
% 4.06/0.99      | k1_relat_1(X0) != sK5
% 4.06/0.99      | sK7 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_9368,c_44,c_46,c_3274]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14597,plain,
% 4.06/0.99      ( k1_relat_1(X0) != sK5
% 4.06/0.99      | sK7 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK7),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_14596]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14608,plain,
% 4.06/0.99      ( sK8 = sK7
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(sK8,sK7),k1_relat_1(sK8)) = iProver_top
% 4.06/0.99      | v1_relat_1(sK8) != iProver_top
% 4.06/0.99      | v1_funct_1(sK8) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4732,c_14597]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_40,negated_conjecture,
% 4.06/0.99      ( v1_funct_1(sK8) ),
% 4.06/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_47,plain,
% 4.06/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_49,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_36,negated_conjecture,
% 4.06/0.99      ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
% 4.06/0.99      inference(cnf_transformation,[],[f108]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3270,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | v1_relat_1(sK8) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3271,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 4.06/0.99      | v1_relat_1(sK8) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3270]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_28,plain,
% 4.06/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 4.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.06/0.99      inference(cnf_transformation,[],[f111]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3336,plain,
% 4.06/0.99      ( r2_relset_1(sK5,sK6,sK7,sK7)
% 4.06/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_29,plain,
% 4.06/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.06/0.99      | X3 = X2 ),
% 4.06/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3502,plain,
% 4.06/0.99      ( ~ r2_relset_1(sK5,sK6,sK7,sK7)
% 4.06/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | sK7 = sK7 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1961,plain,( X0 = X0 ),theory(equality) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3633,plain,
% 4.06/0.99      ( sK6 = sK6 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1961]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3793,plain,
% 4.06/0.99      ( sK5 = sK5 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1961]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1970,plain,
% 4.06/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.06/0.99      | r2_relset_1(X4,X5,X6,X7)
% 4.06/0.99      | X4 != X0
% 4.06/0.99      | X5 != X1
% 4.06/0.99      | X6 != X2
% 4.06/0.99      | X7 != X3 ),
% 4.06/0.99      theory(equality) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3501,plain,
% 4.06/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 4.06/0.99      | ~ r2_relset_1(sK5,sK6,sK7,sK7)
% 4.06/0.99      | X2 != sK7
% 4.06/0.99      | X3 != sK7
% 4.06/0.99      | X1 != sK6
% 4.06/0.99      | X0 != sK5 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1970]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4048,plain,
% 4.06/0.99      ( r2_relset_1(sK5,sK6,sK7,sK8)
% 4.06/0.99      | ~ r2_relset_1(sK5,sK6,sK7,sK7)
% 4.06/0.99      | sK8 != sK7
% 4.06/0.99      | sK7 != sK7
% 4.06/0.99      | sK6 != sK6
% 4.06/0.99      | sK5 != sK5 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_3501]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14738,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(sK8,sK7),k1_relat_1(sK8)) = iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_14608,c_41,c_47,c_49,c_36,c_3271,c_3336,c_3502,c_3633,
% 4.06/0.99                 c_3793,c_4048]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14744,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK2(sK8,sK7),sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4732,c_14738]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_1962,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3286,plain,
% 4.06/0.99      ( sK6 != X0 | sK6 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1962]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3632,plain,
% 4.06/0.99      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_3286]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5495,plain,
% 4.06/0.99      ( X0 != X1 | X1 = X0 ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_1962,c_1961]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15073,plain,
% 4.06/0.99      ( sK5 = k1_relset_1(sK5,sK6,sK8) | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_5495,c_680]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_10,plain,
% 4.06/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 4.06/0.99      | k1_xboole_0 = X0
% 4.06/0.99      | k1_xboole_0 = X1 ),
% 4.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_117,plain,
% 4.06/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.06/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9,plain,
% 4.06/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f110]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_118,plain,
% 4.06/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9520,plain,
% 4.06/0.99      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1962]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9521,plain,
% 4.06/0.99      ( sK6 != k1_xboole_0
% 4.06/0.99      | k1_xboole_0 = sK6
% 4.06/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_9520]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4384,plain,
% 4.06/0.99      ( k1_relat_1(sK8) != X0
% 4.06/0.99      | k1_relat_1(sK8) = k1_relat_1(sK7)
% 4.06/0.99      | k1_relat_1(sK7) != X0 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_1962]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_12709,plain,
% 4.06/0.99      ( k1_relat_1(sK8) = k1_relat_1(sK7)
% 4.06/0.99      | k1_relat_1(sK8) != sK5
% 4.06/0.99      | k1_relat_1(sK7) != sK5 ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_4384]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_9367,plain,
% 4.06/0.99      ( k1_relat_1(X0) != sK5
% 4.06/0.99      | sK8 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top
% 4.06/0.99      | v1_relat_1(sK8) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(sK8) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4732,c_2875]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13250,plain,
% 4.06/0.99      ( v1_funct_1(X0) != iProver_top
% 4.06/0.99      | k1_relat_1(X0) != sK5
% 4.06/0.99      | sK8 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_9367,c_47,c_49,c_3271]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13251,plain,
% 4.06/0.99      ( k1_relat_1(X0) != sK5
% 4.06/0.99      | sK8 = X0
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(X0,sK8),k1_relat_1(X0)) = iProver_top
% 4.06/0.99      | v1_relat_1(X0) != iProver_top
% 4.06/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_13250]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13263,plain,
% 4.06/0.99      ( sK8 = sK7
% 4.06/0.99      | sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(sK7,sK8),k1_relat_1(sK7)) = iProver_top
% 4.06/0.99      | v1_relat_1(sK7) != iProver_top
% 4.06/0.99      | v1_funct_1(sK7) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4735,c_13251]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14347,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0
% 4.06/0.99      | r2_hidden(sK2(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_13263,c_44,c_41,c_46,c_36,c_3274,c_3336,c_3502,c_3633,
% 4.06/0.99                 c_3793,c_4048]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14353,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK2(sK7,sK8),sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_4735,c_14347]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_12,plain,
% 4.06/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2880,plain,
% 4.06/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 4.06/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14584,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0 | m1_subset_1(sK2(sK7,sK8),sK5) = iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_14353,c_2880]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_37,negated_conjecture,
% 4.06/0.99      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f107]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15060,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK8,X0) = k1_funct_1(sK7,X0) ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_5495,c_37]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_17,plain,
% 4.06/0.99      ( ~ v1_relat_1(X0)
% 4.06/0.99      | ~ v1_relat_1(X1)
% 4.06/0.99      | ~ v1_funct_1(X0)
% 4.06/0.99      | ~ v1_funct_1(X1)
% 4.06/0.99      | X0 = X1
% 4.06/0.99      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 4.06/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15294,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK2(sK7,sK8),sK5)
% 4.06/0.99      | ~ v1_relat_1(sK8)
% 4.06/0.99      | ~ v1_relat_1(sK7)
% 4.06/0.99      | ~ v1_funct_1(sK8)
% 4.06/0.99      | ~ v1_funct_1(sK7)
% 4.06/0.99      | k1_relat_1(sK8) != k1_relat_1(sK7)
% 4.06/0.99      | sK8 = sK7 ),
% 4.06/0.99      inference(resolution,[status(thm)],[c_15060,c_17]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15295,plain,
% 4.06/0.99      ( k1_relat_1(sK8) != k1_relat_1(sK7)
% 4.06/0.99      | sK8 = sK7
% 4.06/0.99      | m1_subset_1(sK2(sK7,sK8),sK5) != iProver_top
% 4.06/0.99      | v1_relat_1(sK8) != iProver_top
% 4.06/0.99      | v1_relat_1(sK7) != iProver_top
% 4.06/0.99      | v1_funct_1(sK8) != iProver_top
% 4.06/0.99      | v1_funct_1(sK7) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_15294]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15333,plain,
% 4.06/0.99      ( k1_xboole_0 = sK6 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_15073,c_44,c_41,c_46,c_47,c_49,c_36,c_117,c_118,
% 4.06/0.99                 c_3271,c_3274,c_3336,c_3502,c_3633,c_3793,c_4048,c_4732,
% 4.06/0.99                 c_4735,c_9521,c_12709,c_14584,c_15295]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15652,plain,
% 4.06/0.99      ( sK6 = k1_xboole_0 ),
% 4.06/0.99      inference(global_propositional_subsumption,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_14744,c_44,c_41,c_46,c_47,c_49,c_36,c_3271,c_3274,
% 4.06/0.99                 c_3336,c_3502,c_3633,c_3793,c_4048,c_4732,c_4735,
% 4.06/0.99                 c_12709,c_14584,c_15295]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15716,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_15652,c_2861]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_8,plain,
% 4.06/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.99      inference(cnf_transformation,[],[f109]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15722,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_15716,c_8]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15717,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_15652,c_2859]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_15719,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.06/0.99      inference(demodulation,[status(thm)],[c_15717,c_8]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14508,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) | r1_tarski(sK7,X0) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14509,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | r1_tarski(sK7,X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_14508]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_14511,plain,
% 4.06/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.06/0.99      | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_14509]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7359,plain,
% 4.06/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0)) | r1_tarski(sK8,X0) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7360,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
% 4.06/0.99      | r1_tarski(sK8,X0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_7359]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_7362,plain,
% 4.06/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.06/0.99      | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_7360]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_16,plain,
% 4.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.06/0.99      | ~ r2_hidden(X2,X0)
% 4.06/0.99      | ~ v1_xboole_0(X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_13,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.06/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_314,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.06/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_315,plain,
% 4.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.06/0.99      inference(renaming,[status(thm)],[c_314]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_398,plain,
% 4.06/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 4.06/0.99      inference(bin_hyper_res,[status(thm)],[c_16,c_315]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3616,plain,
% 4.06/0.99      ( ~ r1_tarski(sK7,X0)
% 4.06/0.99      | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,X1,sK7),sK4(sK5,sK6,X1,sK7)),sK7)
% 4.06/0.99      | ~ v1_xboole_0(X0) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_398]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5436,plain,
% 4.06/0.99      ( ~ r1_tarski(sK7,X0)
% 4.06/0.99      | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7)
% 4.06/0.99      | ~ v1_xboole_0(X0) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_3616]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5437,plain,
% 4.06/0.99      ( r1_tarski(sK7,X0) != iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_5436]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5439,plain,
% 4.06/0.99      ( r1_tarski(sK7,k1_xboole_0) != iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) != iProver_top
% 4.06/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_5437]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4349,plain,
% 4.06/0.99      ( ~ r1_tarski(sK8,X0)
% 4.06/0.99      | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8)
% 4.06/0.99      | ~ v1_xboole_0(X0) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_398]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4350,plain,
% 4.06/0.99      ( r1_tarski(sK8,X0) != iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) != iProver_top
% 4.06/0.99      | v1_xboole_0(X0) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4349]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_4352,plain,
% 4.06/0.99      ( r1_tarski(sK8,k1_xboole_0) != iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) != iProver_top
% 4.06/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_4350]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_22,plain,
% 4.06/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 4.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) ),
% 4.06/0.99      inference(cnf_transformation,[],[f90]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3395,plain,
% 4.06/0.99      ( r2_relset_1(sK5,sK6,X0,sK7)
% 4.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,X0,sK7),sK4(sK5,sK6,X0,sK7)),X0)
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,X0,sK7),sK4(sK5,sK6,X0,sK7)),sK7) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3886,plain,
% 4.06/0.99      ( r2_relset_1(sK5,sK6,sK8,sK7)
% 4.06/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8)
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) ),
% 4.06/0.99      inference(instantiation,[status(thm)],[c_3395]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3887,plain,
% 4.06/0.99      ( r2_relset_1(sK5,sK6,sK8,sK7) = iProver_top
% 4.06/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 4.06/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK8) = iProver_top
% 4.06/0.99      | r2_hidden(k4_tarski(sK3(sK5,sK6,sK8,sK7),sK4(sK5,sK6,sK8,sK7)),sK7) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3886]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_2864,plain,
% 4.06/0.99      ( X0 = X1
% 4.06/0.99      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 4.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3405,plain,
% 4.06/0.99      ( sK8 = X0
% 4.06/0.99      | r2_relset_1(sK5,sK6,sK8,X0) != iProver_top
% 4.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2861,c_2864]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_3641,plain,
% 4.06/0.99      ( sK8 = sK7 | r2_relset_1(sK5,sK6,sK8,sK7) != iProver_top ),
% 4.06/0.99      inference(superposition,[status(thm)],[c_2859,c_3405]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_5,plain,
% 4.06/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 4.06/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(c_123,plain,
% 4.06/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.06/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.06/0.99  
% 4.06/0.99  cnf(contradiction,plain,
% 4.06/0.99      ( $false ),
% 4.06/0.99      inference(minisat,
% 4.06/0.99                [status(thm)],
% 4.06/0.99                [c_15722,c_15719,c_14511,c_7362,c_5439,c_4352,c_4048,
% 4.06/0.99                 c_3887,c_3793,c_3641,c_3633,c_3502,c_3336,c_123,c_36,
% 4.06/0.99                 c_49,c_46,c_41]) ).
% 4.06/0.99  
% 4.06/0.99  
% 4.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.06/0.99  
% 4.06/0.99  ------                               Statistics
% 4.06/0.99  
% 4.06/0.99  ------ Selected
% 4.06/0.99  
% 4.06/0.99  total_time:                             0.443
% 4.06/0.99  
%------------------------------------------------------------------------------
