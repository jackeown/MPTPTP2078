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
% DateTime   : Thu Dec  3 12:01:11 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  168 (16017 expanded)
%              Number of clauses        :  112 (4735 expanded)
%              Number of leaves         :   16 (4084 expanded)
%              Depth                    :   30
%              Number of atoms          :  575 (107457 expanded)
%              Number of equality atoms :  328 (25432 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f29,f46,f45])).

fof(f78,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_645,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4993,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK5))
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_4995,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4993])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_432,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_28])).

cnf(c_1089,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1091,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1481,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1089,c_1091])).

cnf(c_1664,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_432,c_1481])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_441,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_443,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_31])).

cnf(c_1087,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1482,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1087,c_1091])).

cnf(c_1742,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_443,c_1482])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1094,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2509,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_1094])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1321,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_2802,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_37,c_39,c_1321])).

cnf(c_2803,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2802])).

cnf(c_2815,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_2803])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1324,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_2887,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2815,c_34,c_36,c_1324])).

cnf(c_2894,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_2887])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1090,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2915,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2894,c_1090])).

cnf(c_643,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1467,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_644,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1354,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_1788,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_19,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_28])).

cnf(c_2968,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_3033,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2915,c_28,c_1467,c_1788,c_2968])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1095,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3144,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_1095])).

cnf(c_3160,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3144])).

cnf(c_3613,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3144,c_33,c_31,c_30,c_28,c_1320,c_1323,c_1467,c_1788,c_2968,c_3160])).

cnf(c_3617,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1664,c_3613])).

cnf(c_3618,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_1742])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK6 != X0
    | sK4 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_404,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1082,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1201,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1082,c_10])).

cnf(c_3630,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_1201])).

cnf(c_3637,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_1089])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3643,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3637,c_9])).

cnf(c_3663,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3630,c_3643])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1083,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1208,plain,
    ( sK5 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1083,c_9])).

cnf(c_3629,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_1208])).

cnf(c_3666,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3629])).

cnf(c_3638,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_1087])).

cnf(c_3640,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_9])).

cnf(c_3670,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3666,c_3640])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK6 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_368,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1084,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1217,plain,
    ( sK6 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1084,c_9])).

cnf(c_1355,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_3935,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3670,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,c_3640,c_3643])).

cnf(c_4538,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3663,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,c_3640,c_3643])).

cnf(c_3633,plain,
    ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_3618,c_1481])).

cnf(c_4036,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_3633,c_3935])).

cnf(c_4541,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4538,c_4036])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK5 != X0
    | sK4 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1081,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1194,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1081,c_10])).

cnf(c_3631,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_1194])).

cnf(c_3657,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3631,c_3640])).

cnf(c_4530,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3657,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,c_3640,c_3643])).

cnf(c_3632,plain,
    ( k1_relset_1(sK3,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_3618,c_1482])).

cnf(c_3996,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_3632,c_3935])).

cnf(c_4533,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4530,c_3996])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3072,plain,
    ( ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1946,plain,
    ( k1_relat_1(sK6) != X0
    | k1_relat_1(sK6) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_1947,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK5)
    | k1_relat_1(sK6) != k1_xboole_0
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_1428,plain,
    ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | X0 = sK5
    | k1_relat_1(X0) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1728,plain,
    ( r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4995,c_4541,c_4533,c_3072,c_2968,c_1947,c_1788,c_1728,c_1467,c_1323,c_1320,c_5,c_28,c_30,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:19:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.94/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/0.96  
% 2.94/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/0.96  
% 2.94/0.96  ------  iProver source info
% 2.94/0.96  
% 2.94/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.94/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/0.96  git: non_committed_changes: false
% 2.94/0.96  git: last_make_outside_of_git: false
% 2.94/0.96  
% 2.94/0.96  ------ 
% 2.94/0.96  
% 2.94/0.96  ------ Input Options
% 2.94/0.96  
% 2.94/0.96  --out_options                           all
% 2.94/0.96  --tptp_safe_out                         true
% 2.94/0.96  --problem_path                          ""
% 2.94/0.96  --include_path                          ""
% 2.94/0.96  --clausifier                            res/vclausify_rel
% 2.94/0.96  --clausifier_options                    --mode clausify
% 2.94/0.96  --stdin                                 false
% 2.94/0.96  --stats_out                             all
% 2.94/0.96  
% 2.94/0.96  ------ General Options
% 2.94/0.96  
% 2.94/0.96  --fof                                   false
% 2.94/0.96  --time_out_real                         305.
% 2.94/0.96  --time_out_virtual                      -1.
% 2.94/0.96  --symbol_type_check                     false
% 2.94/0.96  --clausify_out                          false
% 2.94/0.96  --sig_cnt_out                           false
% 2.94/0.96  --trig_cnt_out                          false
% 2.94/0.96  --trig_cnt_out_tolerance                1.
% 2.94/0.96  --trig_cnt_out_sk_spl                   false
% 2.94/0.96  --abstr_cl_out                          false
% 2.94/0.96  
% 2.94/0.96  ------ Global Options
% 2.94/0.96  
% 2.94/0.96  --schedule                              default
% 2.94/0.96  --add_important_lit                     false
% 2.94/0.96  --prop_solver_per_cl                    1000
% 2.94/0.96  --min_unsat_core                        false
% 2.94/0.96  --soft_assumptions                      false
% 2.94/0.96  --soft_lemma_size                       3
% 2.94/0.96  --prop_impl_unit_size                   0
% 2.94/0.96  --prop_impl_unit                        []
% 2.94/0.96  --share_sel_clauses                     true
% 2.94/0.96  --reset_solvers                         false
% 2.94/0.96  --bc_imp_inh                            [conj_cone]
% 2.94/0.96  --conj_cone_tolerance                   3.
% 2.94/0.96  --extra_neg_conj                        none
% 2.94/0.96  --large_theory_mode                     true
% 2.94/0.96  --prolific_symb_bound                   200
% 2.94/0.96  --lt_threshold                          2000
% 2.94/0.96  --clause_weak_htbl                      true
% 2.94/0.96  --gc_record_bc_elim                     false
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing Options
% 2.94/0.96  
% 2.94/0.96  --preprocessing_flag                    true
% 2.94/0.96  --time_out_prep_mult                    0.1
% 2.94/0.96  --splitting_mode                        input
% 2.94/0.96  --splitting_grd                         true
% 2.94/0.96  --splitting_cvd                         false
% 2.94/0.96  --splitting_cvd_svl                     false
% 2.94/0.96  --splitting_nvd                         32
% 2.94/0.96  --sub_typing                            true
% 2.94/0.96  --prep_gs_sim                           true
% 2.94/0.96  --prep_unflatten                        true
% 2.94/0.96  --prep_res_sim                          true
% 2.94/0.96  --prep_upred                            true
% 2.94/0.96  --prep_sem_filter                       exhaustive
% 2.94/0.96  --prep_sem_filter_out                   false
% 2.94/0.96  --pred_elim                             true
% 2.94/0.96  --res_sim_input                         true
% 2.94/0.96  --eq_ax_congr_red                       true
% 2.94/0.96  --pure_diseq_elim                       true
% 2.94/0.96  --brand_transform                       false
% 2.94/0.96  --non_eq_to_eq                          false
% 2.94/0.96  --prep_def_merge                        true
% 2.94/0.96  --prep_def_merge_prop_impl              false
% 2.94/0.96  --prep_def_merge_mbd                    true
% 2.94/0.96  --prep_def_merge_tr_red                 false
% 2.94/0.96  --prep_def_merge_tr_cl                  false
% 2.94/0.96  --smt_preprocessing                     true
% 2.94/0.96  --smt_ac_axioms                         fast
% 2.94/0.96  --preprocessed_out                      false
% 2.94/0.96  --preprocessed_stats                    false
% 2.94/0.96  
% 2.94/0.96  ------ Abstraction refinement Options
% 2.94/0.96  
% 2.94/0.96  --abstr_ref                             []
% 2.94/0.96  --abstr_ref_prep                        false
% 2.94/0.96  --abstr_ref_until_sat                   false
% 2.94/0.96  --abstr_ref_sig_restrict                funpre
% 2.94/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.96  --abstr_ref_under                       []
% 2.94/0.96  
% 2.94/0.96  ------ SAT Options
% 2.94/0.96  
% 2.94/0.96  --sat_mode                              false
% 2.94/0.96  --sat_fm_restart_options                ""
% 2.94/0.96  --sat_gr_def                            false
% 2.94/0.96  --sat_epr_types                         true
% 2.94/0.96  --sat_non_cyclic_types                  false
% 2.94/0.96  --sat_finite_models                     false
% 2.94/0.96  --sat_fm_lemmas                         false
% 2.94/0.96  --sat_fm_prep                           false
% 2.94/0.96  --sat_fm_uc_incr                        true
% 2.94/0.96  --sat_out_model                         small
% 2.94/0.96  --sat_out_clauses                       false
% 2.94/0.96  
% 2.94/0.96  ------ QBF Options
% 2.94/0.96  
% 2.94/0.96  --qbf_mode                              false
% 2.94/0.96  --qbf_elim_univ                         false
% 2.94/0.96  --qbf_dom_inst                          none
% 2.94/0.96  --qbf_dom_pre_inst                      false
% 2.94/0.96  --qbf_sk_in                             false
% 2.94/0.96  --qbf_pred_elim                         true
% 2.94/0.96  --qbf_split                             512
% 2.94/0.96  
% 2.94/0.96  ------ BMC1 Options
% 2.94/0.96  
% 2.94/0.96  --bmc1_incremental                      false
% 2.94/0.96  --bmc1_axioms                           reachable_all
% 2.94/0.96  --bmc1_min_bound                        0
% 2.94/0.96  --bmc1_max_bound                        -1
% 2.94/0.96  --bmc1_max_bound_default                -1
% 2.94/0.96  --bmc1_symbol_reachability              true
% 2.94/0.96  --bmc1_property_lemmas                  false
% 2.94/0.96  --bmc1_k_induction                      false
% 2.94/0.96  --bmc1_non_equiv_states                 false
% 2.94/0.96  --bmc1_deadlock                         false
% 2.94/0.96  --bmc1_ucm                              false
% 2.94/0.96  --bmc1_add_unsat_core                   none
% 2.94/0.96  --bmc1_unsat_core_children              false
% 2.94/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.96  --bmc1_out_stat                         full
% 2.94/0.96  --bmc1_ground_init                      false
% 2.94/0.96  --bmc1_pre_inst_next_state              false
% 2.94/0.96  --bmc1_pre_inst_state                   false
% 2.94/0.96  --bmc1_pre_inst_reach_state             false
% 2.94/0.96  --bmc1_out_unsat_core                   false
% 2.94/0.96  --bmc1_aig_witness_out                  false
% 2.94/0.96  --bmc1_verbose                          false
% 2.94/0.96  --bmc1_dump_clauses_tptp                false
% 2.94/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.96  --bmc1_dump_file                        -
% 2.94/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.96  --bmc1_ucm_extend_mode                  1
% 2.94/0.96  --bmc1_ucm_init_mode                    2
% 2.94/0.96  --bmc1_ucm_cone_mode                    none
% 2.94/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.96  --bmc1_ucm_relax_model                  4
% 2.94/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.96  --bmc1_ucm_layered_model                none
% 2.94/0.96  --bmc1_ucm_max_lemma_size               10
% 2.94/0.96  
% 2.94/0.96  ------ AIG Options
% 2.94/0.96  
% 2.94/0.96  --aig_mode                              false
% 2.94/0.96  
% 2.94/0.96  ------ Instantiation Options
% 2.94/0.96  
% 2.94/0.96  --instantiation_flag                    true
% 2.94/0.96  --inst_sos_flag                         false
% 2.94/0.96  --inst_sos_phase                        true
% 2.94/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.96  --inst_lit_sel_side                     num_symb
% 2.94/0.96  --inst_solver_per_active                1400
% 2.94/0.96  --inst_solver_calls_frac                1.
% 2.94/0.96  --inst_passive_queue_type               priority_queues
% 2.94/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.96  --inst_passive_queues_freq              [25;2]
% 2.94/0.96  --inst_dismatching                      true
% 2.94/0.96  --inst_eager_unprocessed_to_passive     true
% 2.94/0.96  --inst_prop_sim_given                   true
% 2.94/0.96  --inst_prop_sim_new                     false
% 2.94/0.96  --inst_subs_new                         false
% 2.94/0.96  --inst_eq_res_simp                      false
% 2.94/0.96  --inst_subs_given                       false
% 2.94/0.96  --inst_orphan_elimination               true
% 2.94/0.96  --inst_learning_loop_flag               true
% 2.94/0.96  --inst_learning_start                   3000
% 2.94/0.96  --inst_learning_factor                  2
% 2.94/0.96  --inst_start_prop_sim_after_learn       3
% 2.94/0.96  --inst_sel_renew                        solver
% 2.94/0.96  --inst_lit_activity_flag                true
% 2.94/0.96  --inst_restr_to_given                   false
% 2.94/0.96  --inst_activity_threshold               500
% 2.94/0.96  --inst_out_proof                        true
% 2.94/0.96  
% 2.94/0.96  ------ Resolution Options
% 2.94/0.96  
% 2.94/0.96  --resolution_flag                       true
% 2.94/0.96  --res_lit_sel                           adaptive
% 2.94/0.96  --res_lit_sel_side                      none
% 2.94/0.96  --res_ordering                          kbo
% 2.94/0.96  --res_to_prop_solver                    active
% 2.94/0.96  --res_prop_simpl_new                    false
% 2.94/0.96  --res_prop_simpl_given                  true
% 2.94/0.96  --res_passive_queue_type                priority_queues
% 2.94/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.96  --res_passive_queues_freq               [15;5]
% 2.94/0.96  --res_forward_subs                      full
% 2.94/0.96  --res_backward_subs                     full
% 2.94/0.96  --res_forward_subs_resolution           true
% 2.94/0.96  --res_backward_subs_resolution          true
% 2.94/0.96  --res_orphan_elimination                true
% 2.94/0.96  --res_time_limit                        2.
% 2.94/0.96  --res_out_proof                         true
% 2.94/0.96  
% 2.94/0.96  ------ Superposition Options
% 2.94/0.96  
% 2.94/0.96  --superposition_flag                    true
% 2.94/0.96  --sup_passive_queue_type                priority_queues
% 2.94/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.96  --demod_completeness_check              fast
% 2.94/0.96  --demod_use_ground                      true
% 2.94/0.96  --sup_to_prop_solver                    passive
% 2.94/0.96  --sup_prop_simpl_new                    true
% 2.94/0.96  --sup_prop_simpl_given                  true
% 2.94/0.96  --sup_fun_splitting                     false
% 2.94/0.96  --sup_smt_interval                      50000
% 2.94/0.96  
% 2.94/0.96  ------ Superposition Simplification Setup
% 2.94/0.96  
% 2.94/0.96  --sup_indices_passive                   []
% 2.94/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_full_bw                           [BwDemod]
% 2.94/0.96  --sup_immed_triv                        [TrivRules]
% 2.94/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_immed_bw_main                     []
% 2.94/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.96  
% 2.94/0.96  ------ Combination Options
% 2.94/0.96  
% 2.94/0.96  --comb_res_mult                         3
% 2.94/0.96  --comb_sup_mult                         2
% 2.94/0.96  --comb_inst_mult                        10
% 2.94/0.96  
% 2.94/0.96  ------ Debug Options
% 2.94/0.96  
% 2.94/0.96  --dbg_backtrace                         false
% 2.94/0.96  --dbg_dump_prop_clauses                 false
% 2.94/0.96  --dbg_dump_prop_clauses_file            -
% 2.94/0.96  --dbg_out_stat                          false
% 2.94/0.96  ------ Parsing...
% 2.94/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/0.96  ------ Proving...
% 2.94/0.96  ------ Problem Properties 
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  clauses                                 30
% 2.94/0.96  conjectures                             5
% 2.94/0.96  EPR                                     7
% 2.94/0.96  Horn                                    22
% 2.94/0.96  unary                                   9
% 2.94/0.96  binary                                  10
% 2.94/0.96  lits                                    72
% 2.94/0.96  lits eq                                 28
% 2.94/0.96  fd_pure                                 0
% 2.94/0.96  fd_pseudo                               0
% 2.94/0.96  fd_cond                                 1
% 2.94/0.96  fd_pseudo_cond                          3
% 2.94/0.96  AC symbols                              0
% 2.94/0.96  
% 2.94/0.96  ------ Schedule dynamic 5 is on 
% 2.94/0.96  
% 2.94/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  ------ 
% 2.94/0.96  Current options:
% 2.94/0.96  ------ 
% 2.94/0.96  
% 2.94/0.96  ------ Input Options
% 2.94/0.96  
% 2.94/0.96  --out_options                           all
% 2.94/0.96  --tptp_safe_out                         true
% 2.94/0.96  --problem_path                          ""
% 2.94/0.96  --include_path                          ""
% 2.94/0.96  --clausifier                            res/vclausify_rel
% 2.94/0.96  --clausifier_options                    --mode clausify
% 2.94/0.96  --stdin                                 false
% 2.94/0.96  --stats_out                             all
% 2.94/0.96  
% 2.94/0.96  ------ General Options
% 2.94/0.96  
% 2.94/0.96  --fof                                   false
% 2.94/0.96  --time_out_real                         305.
% 2.94/0.96  --time_out_virtual                      -1.
% 2.94/0.96  --symbol_type_check                     false
% 2.94/0.96  --clausify_out                          false
% 2.94/0.96  --sig_cnt_out                           false
% 2.94/0.96  --trig_cnt_out                          false
% 2.94/0.96  --trig_cnt_out_tolerance                1.
% 2.94/0.96  --trig_cnt_out_sk_spl                   false
% 2.94/0.96  --abstr_cl_out                          false
% 2.94/0.96  
% 2.94/0.96  ------ Global Options
% 2.94/0.96  
% 2.94/0.96  --schedule                              default
% 2.94/0.96  --add_important_lit                     false
% 2.94/0.96  --prop_solver_per_cl                    1000
% 2.94/0.96  --min_unsat_core                        false
% 2.94/0.96  --soft_assumptions                      false
% 2.94/0.96  --soft_lemma_size                       3
% 2.94/0.96  --prop_impl_unit_size                   0
% 2.94/0.96  --prop_impl_unit                        []
% 2.94/0.96  --share_sel_clauses                     true
% 2.94/0.96  --reset_solvers                         false
% 2.94/0.96  --bc_imp_inh                            [conj_cone]
% 2.94/0.96  --conj_cone_tolerance                   3.
% 2.94/0.96  --extra_neg_conj                        none
% 2.94/0.96  --large_theory_mode                     true
% 2.94/0.96  --prolific_symb_bound                   200
% 2.94/0.96  --lt_threshold                          2000
% 2.94/0.96  --clause_weak_htbl                      true
% 2.94/0.96  --gc_record_bc_elim                     false
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing Options
% 2.94/0.96  
% 2.94/0.96  --preprocessing_flag                    true
% 2.94/0.96  --time_out_prep_mult                    0.1
% 2.94/0.96  --splitting_mode                        input
% 2.94/0.96  --splitting_grd                         true
% 2.94/0.96  --splitting_cvd                         false
% 2.94/0.96  --splitting_cvd_svl                     false
% 2.94/0.96  --splitting_nvd                         32
% 2.94/0.96  --sub_typing                            true
% 2.94/0.96  --prep_gs_sim                           true
% 2.94/0.96  --prep_unflatten                        true
% 2.94/0.96  --prep_res_sim                          true
% 2.94/0.96  --prep_upred                            true
% 2.94/0.96  --prep_sem_filter                       exhaustive
% 2.94/0.96  --prep_sem_filter_out                   false
% 2.94/0.96  --pred_elim                             true
% 2.94/0.96  --res_sim_input                         true
% 2.94/0.96  --eq_ax_congr_red                       true
% 2.94/0.96  --pure_diseq_elim                       true
% 2.94/0.96  --brand_transform                       false
% 2.94/0.96  --non_eq_to_eq                          false
% 2.94/0.96  --prep_def_merge                        true
% 2.94/0.96  --prep_def_merge_prop_impl              false
% 2.94/0.96  --prep_def_merge_mbd                    true
% 2.94/0.96  --prep_def_merge_tr_red                 false
% 2.94/0.96  --prep_def_merge_tr_cl                  false
% 2.94/0.96  --smt_preprocessing                     true
% 2.94/0.96  --smt_ac_axioms                         fast
% 2.94/0.96  --preprocessed_out                      false
% 2.94/0.96  --preprocessed_stats                    false
% 2.94/0.96  
% 2.94/0.96  ------ Abstraction refinement Options
% 2.94/0.96  
% 2.94/0.96  --abstr_ref                             []
% 2.94/0.96  --abstr_ref_prep                        false
% 2.94/0.96  --abstr_ref_until_sat                   false
% 2.94/0.96  --abstr_ref_sig_restrict                funpre
% 2.94/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.96  --abstr_ref_under                       []
% 2.94/0.96  
% 2.94/0.96  ------ SAT Options
% 2.94/0.96  
% 2.94/0.96  --sat_mode                              false
% 2.94/0.96  --sat_fm_restart_options                ""
% 2.94/0.96  --sat_gr_def                            false
% 2.94/0.96  --sat_epr_types                         true
% 2.94/0.96  --sat_non_cyclic_types                  false
% 2.94/0.96  --sat_finite_models                     false
% 2.94/0.96  --sat_fm_lemmas                         false
% 2.94/0.96  --sat_fm_prep                           false
% 2.94/0.96  --sat_fm_uc_incr                        true
% 2.94/0.96  --sat_out_model                         small
% 2.94/0.96  --sat_out_clauses                       false
% 2.94/0.96  
% 2.94/0.96  ------ QBF Options
% 2.94/0.96  
% 2.94/0.96  --qbf_mode                              false
% 2.94/0.96  --qbf_elim_univ                         false
% 2.94/0.96  --qbf_dom_inst                          none
% 2.94/0.96  --qbf_dom_pre_inst                      false
% 2.94/0.96  --qbf_sk_in                             false
% 2.94/0.96  --qbf_pred_elim                         true
% 2.94/0.96  --qbf_split                             512
% 2.94/0.96  
% 2.94/0.96  ------ BMC1 Options
% 2.94/0.96  
% 2.94/0.96  --bmc1_incremental                      false
% 2.94/0.96  --bmc1_axioms                           reachable_all
% 2.94/0.96  --bmc1_min_bound                        0
% 2.94/0.96  --bmc1_max_bound                        -1
% 2.94/0.96  --bmc1_max_bound_default                -1
% 2.94/0.96  --bmc1_symbol_reachability              true
% 2.94/0.96  --bmc1_property_lemmas                  false
% 2.94/0.96  --bmc1_k_induction                      false
% 2.94/0.96  --bmc1_non_equiv_states                 false
% 2.94/0.96  --bmc1_deadlock                         false
% 2.94/0.96  --bmc1_ucm                              false
% 2.94/0.96  --bmc1_add_unsat_core                   none
% 2.94/0.96  --bmc1_unsat_core_children              false
% 2.94/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.96  --bmc1_out_stat                         full
% 2.94/0.96  --bmc1_ground_init                      false
% 2.94/0.96  --bmc1_pre_inst_next_state              false
% 2.94/0.96  --bmc1_pre_inst_state                   false
% 2.94/0.96  --bmc1_pre_inst_reach_state             false
% 2.94/0.96  --bmc1_out_unsat_core                   false
% 2.94/0.96  --bmc1_aig_witness_out                  false
% 2.94/0.96  --bmc1_verbose                          false
% 2.94/0.96  --bmc1_dump_clauses_tptp                false
% 2.94/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.96  --bmc1_dump_file                        -
% 2.94/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.96  --bmc1_ucm_extend_mode                  1
% 2.94/0.96  --bmc1_ucm_init_mode                    2
% 2.94/0.96  --bmc1_ucm_cone_mode                    none
% 2.94/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.96  --bmc1_ucm_relax_model                  4
% 2.94/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.96  --bmc1_ucm_layered_model                none
% 2.94/0.96  --bmc1_ucm_max_lemma_size               10
% 2.94/0.96  
% 2.94/0.96  ------ AIG Options
% 2.94/0.96  
% 2.94/0.96  --aig_mode                              false
% 2.94/0.96  
% 2.94/0.96  ------ Instantiation Options
% 2.94/0.96  
% 2.94/0.96  --instantiation_flag                    true
% 2.94/0.96  --inst_sos_flag                         false
% 2.94/0.96  --inst_sos_phase                        true
% 2.94/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.96  --inst_lit_sel_side                     none
% 2.94/0.96  --inst_solver_per_active                1400
% 2.94/0.96  --inst_solver_calls_frac                1.
% 2.94/0.96  --inst_passive_queue_type               priority_queues
% 2.94/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.96  --inst_passive_queues_freq              [25;2]
% 2.94/0.96  --inst_dismatching                      true
% 2.94/0.96  --inst_eager_unprocessed_to_passive     true
% 2.94/0.96  --inst_prop_sim_given                   true
% 2.94/0.96  --inst_prop_sim_new                     false
% 2.94/0.96  --inst_subs_new                         false
% 2.94/0.96  --inst_eq_res_simp                      false
% 2.94/0.96  --inst_subs_given                       false
% 2.94/0.96  --inst_orphan_elimination               true
% 2.94/0.96  --inst_learning_loop_flag               true
% 2.94/0.96  --inst_learning_start                   3000
% 2.94/0.96  --inst_learning_factor                  2
% 2.94/0.96  --inst_start_prop_sim_after_learn       3
% 2.94/0.96  --inst_sel_renew                        solver
% 2.94/0.96  --inst_lit_activity_flag                true
% 2.94/0.96  --inst_restr_to_given                   false
% 2.94/0.96  --inst_activity_threshold               500
% 2.94/0.96  --inst_out_proof                        true
% 2.94/0.96  
% 2.94/0.96  ------ Resolution Options
% 2.94/0.96  
% 2.94/0.96  --resolution_flag                       false
% 2.94/0.96  --res_lit_sel                           adaptive
% 2.94/0.96  --res_lit_sel_side                      none
% 2.94/0.96  --res_ordering                          kbo
% 2.94/0.96  --res_to_prop_solver                    active
% 2.94/0.96  --res_prop_simpl_new                    false
% 2.94/0.96  --res_prop_simpl_given                  true
% 2.94/0.96  --res_passive_queue_type                priority_queues
% 2.94/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.96  --res_passive_queues_freq               [15;5]
% 2.94/0.96  --res_forward_subs                      full
% 2.94/0.96  --res_backward_subs                     full
% 2.94/0.96  --res_forward_subs_resolution           true
% 2.94/0.96  --res_backward_subs_resolution          true
% 2.94/0.96  --res_orphan_elimination                true
% 2.94/0.96  --res_time_limit                        2.
% 2.94/0.96  --res_out_proof                         true
% 2.94/0.96  
% 2.94/0.96  ------ Superposition Options
% 2.94/0.96  
% 2.94/0.96  --superposition_flag                    true
% 2.94/0.96  --sup_passive_queue_type                priority_queues
% 2.94/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.96  --demod_completeness_check              fast
% 2.94/0.96  --demod_use_ground                      true
% 2.94/0.96  --sup_to_prop_solver                    passive
% 2.94/0.96  --sup_prop_simpl_new                    true
% 2.94/0.96  --sup_prop_simpl_given                  true
% 2.94/0.96  --sup_fun_splitting                     false
% 2.94/0.96  --sup_smt_interval                      50000
% 2.94/0.96  
% 2.94/0.96  ------ Superposition Simplification Setup
% 2.94/0.96  
% 2.94/0.96  --sup_indices_passive                   []
% 2.94/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_full_bw                           [BwDemod]
% 2.94/0.96  --sup_immed_triv                        [TrivRules]
% 2.94/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_immed_bw_main                     []
% 2.94/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.96  
% 2.94/0.96  ------ Combination Options
% 2.94/0.96  
% 2.94/0.96  --comb_res_mult                         3
% 2.94/0.96  --comb_sup_mult                         2
% 2.94/0.96  --comb_inst_mult                        10
% 2.94/0.96  
% 2.94/0.96  ------ Debug Options
% 2.94/0.96  
% 2.94/0.96  --dbg_backtrace                         false
% 2.94/0.96  --dbg_dump_prop_clauses                 false
% 2.94/0.96  --dbg_dump_prop_clauses_file            -
% 2.94/0.96  --dbg_out_stat                          false
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  ------ Proving...
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  % SZS status Theorem for theBenchmark.p
% 2.94/0.96  
% 2.94/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/0.96  
% 2.94/0.96  fof(f13,axiom,(
% 2.94/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f26,plain,(
% 2.94/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(ennf_transformation,[],[f13])).
% 2.94/0.96  
% 2.94/0.96  fof(f27,plain,(
% 2.94/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(flattening,[],[f26])).
% 2.94/0.96  
% 2.94/0.96  fof(f44,plain,(
% 2.94/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(nnf_transformation,[],[f27])).
% 2.94/0.96  
% 2.94/0.96  fof(f68,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f44])).
% 2.94/0.96  
% 2.94/0.96  fof(f14,conjecture,(
% 2.94/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f15,negated_conjecture,(
% 2.94/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.94/0.96    inference(negated_conjecture,[],[f14])).
% 2.94/0.96  
% 2.94/0.96  fof(f28,plain,(
% 2.94/0.96    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/0.96    inference(ennf_transformation,[],[f15])).
% 2.94/0.96  
% 2.94/0.96  fof(f29,plain,(
% 2.94/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/0.96    inference(flattening,[],[f28])).
% 2.94/0.96  
% 2.94/0.96  fof(f46,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 2.94/0.96    introduced(choice_axiom,[])).
% 2.94/0.96  
% 2.94/0.96  fof(f45,plain,(
% 2.94/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 2.94/0.96    introduced(choice_axiom,[])).
% 2.94/0.96  
% 2.94/0.96  fof(f47,plain,(
% 2.94/0.96    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 2.94/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f29,f46,f45])).
% 2.94/0.96  
% 2.94/0.96  fof(f78,plain,(
% 2.94/0.96    v1_funct_2(sK6,sK3,sK4)),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f79,plain,(
% 2.94/0.96    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f11,axiom,(
% 2.94/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f23,plain,(
% 2.94/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(ennf_transformation,[],[f11])).
% 2.94/0.96  
% 2.94/0.96  fof(f66,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f23])).
% 2.94/0.96  
% 2.94/0.96  fof(f75,plain,(
% 2.94/0.96    v1_funct_2(sK5,sK3,sK4)),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f76,plain,(
% 2.94/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f8,axiom,(
% 2.94/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f19,plain,(
% 2.94/0.96    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.96    inference(ennf_transformation,[],[f8])).
% 2.94/0.96  
% 2.94/0.96  fof(f20,plain,(
% 2.94/0.96    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.96    inference(flattening,[],[f19])).
% 2.94/0.96  
% 2.94/0.96  fof(f42,plain,(
% 2.94/0.96    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 2.94/0.96    introduced(choice_axiom,[])).
% 2.94/0.96  
% 2.94/0.96  fof(f43,plain,(
% 2.94/0.96    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f42])).
% 2.94/0.96  
% 2.94/0.96  fof(f62,plain,(
% 2.94/0.96    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.96    inference(cnf_transformation,[],[f43])).
% 2.94/0.96  
% 2.94/0.96  fof(f77,plain,(
% 2.94/0.96    v1_funct_1(sK6)),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f9,axiom,(
% 2.94/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f21,plain,(
% 2.94/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(ennf_transformation,[],[f9])).
% 2.94/0.96  
% 2.94/0.96  fof(f64,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f21])).
% 2.94/0.96  
% 2.94/0.96  fof(f74,plain,(
% 2.94/0.96    v1_funct_1(sK5)),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f80,plain,(
% 2.94/0.96    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f12,axiom,(
% 2.94/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f24,plain,(
% 2.94/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.94/0.96    inference(ennf_transformation,[],[f12])).
% 2.94/0.96  
% 2.94/0.96  fof(f25,plain,(
% 2.94/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.96    inference(flattening,[],[f24])).
% 2.94/0.96  
% 2.94/0.96  fof(f67,plain,(
% 2.94/0.96    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f25])).
% 2.94/0.96  
% 2.94/0.96  fof(f81,plain,(
% 2.94/0.96    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 2.94/0.96    inference(cnf_transformation,[],[f47])).
% 2.94/0.96  
% 2.94/0.96  fof(f63,plain,(
% 2.94/0.96    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.96    inference(cnf_transformation,[],[f43])).
% 2.94/0.96  
% 2.94/0.96  fof(f69,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f44])).
% 2.94/0.96  
% 2.94/0.96  fof(f90,plain,(
% 2.94/0.96    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.94/0.96    inference(equality_resolution,[],[f69])).
% 2.94/0.96  
% 2.94/0.96  fof(f5,axiom,(
% 2.94/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f40,plain,(
% 2.94/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.96    inference(nnf_transformation,[],[f5])).
% 2.94/0.96  
% 2.94/0.96  fof(f41,plain,(
% 2.94/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.96    inference(flattening,[],[f40])).
% 2.94/0.96  
% 2.94/0.96  fof(f58,plain,(
% 2.94/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.94/0.96    inference(cnf_transformation,[],[f41])).
% 2.94/0.96  
% 2.94/0.96  fof(f85,plain,(
% 2.94/0.96    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.94/0.96    inference(equality_resolution,[],[f58])).
% 2.94/0.96  
% 2.94/0.96  fof(f59,plain,(
% 2.94/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.94/0.96    inference(cnf_transformation,[],[f41])).
% 2.94/0.96  
% 2.94/0.96  fof(f84,plain,(
% 2.94/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.94/0.96    inference(equality_resolution,[],[f59])).
% 2.94/0.96  
% 2.94/0.96  fof(f72,plain,(
% 2.94/0.96    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.96    inference(cnf_transformation,[],[f44])).
% 2.94/0.96  
% 2.94/0.96  fof(f88,plain,(
% 2.94/0.96    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.94/0.96    inference(equality_resolution,[],[f72])).
% 2.94/0.96  
% 2.94/0.96  fof(f1,axiom,(
% 2.94/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f30,plain,(
% 2.94/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.94/0.96    inference(nnf_transformation,[],[f1])).
% 2.94/0.96  
% 2.94/0.96  fof(f31,plain,(
% 2.94/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.94/0.96    inference(rectify,[],[f30])).
% 2.94/0.96  
% 2.94/0.96  fof(f32,plain,(
% 2.94/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.94/0.96    introduced(choice_axiom,[])).
% 2.94/0.96  
% 2.94/0.96  fof(f33,plain,(
% 2.94/0.96    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.94/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.94/0.96  
% 2.94/0.96  fof(f48,plain,(
% 2.94/0.96    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.94/0.96    inference(cnf_transformation,[],[f33])).
% 2.94/0.96  
% 2.94/0.96  fof(f3,axiom,(
% 2.94/0.96    v1_xboole_0(k1_xboole_0)),
% 2.94/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.96  
% 2.94/0.96  fof(f53,plain,(
% 2.94/0.96    v1_xboole_0(k1_xboole_0)),
% 2.94/0.96    inference(cnf_transformation,[],[f3])).
% 2.94/0.96  
% 2.94/0.96  cnf(c_645,plain,
% 2.94/0.96      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.94/0.96      theory(equality) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4993,plain,
% 2.94/0.96      ( ~ v1_xboole_0(X0)
% 2.94/0.96      | v1_xboole_0(k1_relat_1(sK5))
% 2.94/0.96      | k1_relat_1(sK5) != X0 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_645]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4995,plain,
% 2.94/0.96      ( v1_xboole_0(k1_relat_1(sK5))
% 2.94/0.96      | ~ v1_xboole_0(k1_xboole_0)
% 2.94/0.96      | k1_relat_1(sK5) != k1_xboole_0 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_4993]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_25,plain,
% 2.94/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.96      | k1_xboole_0 = X2 ),
% 2.94/0.96      inference(cnf_transformation,[],[f68]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_29,negated_conjecture,
% 2.94/0.96      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.94/0.96      inference(cnf_transformation,[],[f78]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_429,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.96      | sK6 != X0
% 2.94/0.96      | sK4 != X2
% 2.94/0.96      | sK3 != X1
% 2.94/0.96      | k1_xboole_0 = X2 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_430,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | k1_relset_1(sK3,sK4,sK6) = sK3
% 2.94/0.96      | k1_xboole_0 = sK4 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_429]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_28,negated_conjecture,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.94/0.96      inference(cnf_transformation,[],[f79]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_432,plain,
% 2.94/0.96      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_430,c_28]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1089,plain,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_18,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.94/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1091,plain,
% 2.94/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.94/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1481,plain,
% 2.94/0.96      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1089,c_1091]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1664,plain,
% 2.94/0.96      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_432,c_1481]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_32,negated_conjecture,
% 2.94/0.96      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.94/0.96      inference(cnf_transformation,[],[f75]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_440,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.96      | sK5 != X0
% 2.94/0.96      | sK4 != X2
% 2.94/0.96      | sK3 != X1
% 2.94/0.96      | k1_xboole_0 = X2 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_441,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | k1_relset_1(sK3,sK4,sK5) = sK3
% 2.94/0.96      | k1_xboole_0 = sK4 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_440]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_31,negated_conjecture,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.94/0.96      inference(cnf_transformation,[],[f76]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_443,plain,
% 2.94/0.96      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_441,c_31]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1087,plain,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1482,plain,
% 2.94/0.96      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1087,c_1091]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1742,plain,
% 2.94/0.96      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_443,c_1482]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_15,plain,
% 2.94/0.96      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 2.94/0.96      | ~ v1_relat_1(X1)
% 2.94/0.96      | ~ v1_relat_1(X0)
% 2.94/0.96      | ~ v1_funct_1(X1)
% 2.94/0.96      | ~ v1_funct_1(X0)
% 2.94/0.96      | X1 = X0
% 2.94/0.96      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.94/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1094,plain,
% 2.94/0.96      ( X0 = X1
% 2.94/0.96      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.94/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.94/0.96      | v1_relat_1(X1) != iProver_top
% 2.94/0.96      | v1_relat_1(X0) != iProver_top
% 2.94/0.96      | v1_funct_1(X0) != iProver_top
% 2.94/0.96      | v1_funct_1(X1) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2509,plain,
% 2.94/0.96      ( k1_relat_1(X0) != sK3
% 2.94/0.96      | sK6 = X0
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.94/0.96      | v1_relat_1(X0) != iProver_top
% 2.94/0.96      | v1_relat_1(sK6) != iProver_top
% 2.94/0.96      | v1_funct_1(X0) != iProver_top
% 2.94/0.96      | v1_funct_1(sK6) != iProver_top ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1664,c_1094]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_30,negated_conjecture,
% 2.94/0.96      ( v1_funct_1(sK6) ),
% 2.94/0.96      inference(cnf_transformation,[],[f77]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_37,plain,
% 2.94/0.96      ( v1_funct_1(sK6) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_39,plain,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_16,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | v1_relat_1(X0) ),
% 2.94/0.96      inference(cnf_transformation,[],[f64]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1320,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | v1_relat_1(sK6) ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_16]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1321,plain,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.94/0.96      | v1_relat_1(sK6) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2802,plain,
% 2.94/0.96      ( v1_funct_1(X0) != iProver_top
% 2.94/0.96      | k1_relat_1(X0) != sK3
% 2.94/0.96      | sK6 = X0
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.94/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_2509,c_37,c_39,c_1321]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2803,plain,
% 2.94/0.96      ( k1_relat_1(X0) != sK3
% 2.94/0.96      | sK6 = X0
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.94/0.96      | v1_relat_1(X0) != iProver_top
% 2.94/0.96      | v1_funct_1(X0) != iProver_top ),
% 2.94/0.96      inference(renaming,[status(thm)],[c_2802]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2815,plain,
% 2.94/0.96      ( sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.94/0.96      | v1_relat_1(sK5) != iProver_top
% 2.94/0.96      | v1_funct_1(sK5) != iProver_top ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1742,c_2803]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_33,negated_conjecture,
% 2.94/0.96      ( v1_funct_1(sK5) ),
% 2.94/0.96      inference(cnf_transformation,[],[f74]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_34,plain,
% 2.94/0.96      ( v1_funct_1(sK5) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_36,plain,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1323,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | v1_relat_1(sK5) ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_16]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1324,plain,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.94/0.96      | v1_relat_1(sK5) = iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2887,plain,
% 2.94/0.96      ( sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_2815,c_34,c_36,c_1324]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2894,plain,
% 2.94/0.96      ( sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1742,c_2887]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_27,negated_conjecture,
% 2.94/0.96      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 2.94/0.96      inference(cnf_transformation,[],[f80]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1090,plain,
% 2.94/0.96      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 2.94/0.96      | r2_hidden(X0,sK3) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2915,plain,
% 2.94/0.96      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.94/0.96      | sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_2894,c_1090]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_643,plain,( X0 = X0 ),theory(equality) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1467,plain,
% 2.94/0.96      ( sK5 = sK5 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_643]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_644,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1354,plain,
% 2.94/0.96      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_644]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1788,plain,
% 2.94/0.96      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_19,plain,
% 2.94/0.96      ( r2_relset_1(X0,X1,X2,X2)
% 2.94/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.94/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_26,negated_conjecture,
% 2.94/0.96      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 2.94/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_334,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.96      | sK6 != X0
% 2.94/0.96      | sK5 != X0
% 2.94/0.96      | sK4 != X2
% 2.94/0.96      | sK3 != X1 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_335,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | sK5 != sK6 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_334]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_339,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | sK5 != sK6 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_335,c_28]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_2968,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.94/0.96      | sK5 != sK6 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_339]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3033,plain,
% 2.94/0.96      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.94/0.96      | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_2915,c_28,c_1467,c_1788,c_2968]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_14,plain,
% 2.94/0.96      ( ~ v1_relat_1(X0)
% 2.94/0.96      | ~ v1_relat_1(X1)
% 2.94/0.96      | ~ v1_funct_1(X0)
% 2.94/0.96      | ~ v1_funct_1(X1)
% 2.94/0.96      | X0 = X1
% 2.94/0.96      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.94/0.96      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.94/0.96      inference(cnf_transformation,[],[f63]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1095,plain,
% 2.94/0.96      ( X0 = X1
% 2.94/0.96      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.94/0.96      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.94/0.96      | v1_relat_1(X0) != iProver_top
% 2.94/0.96      | v1_relat_1(X1) != iProver_top
% 2.94/0.96      | v1_funct_1(X1) != iProver_top
% 2.94/0.96      | v1_funct_1(X0) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3144,plain,
% 2.94/0.96      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.94/0.96      | sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0
% 2.94/0.96      | v1_relat_1(sK6) != iProver_top
% 2.94/0.96      | v1_relat_1(sK5) != iProver_top
% 2.94/0.96      | v1_funct_1(sK6) != iProver_top
% 2.94/0.96      | v1_funct_1(sK5) != iProver_top ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_3033,c_1095]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3160,plain,
% 2.94/0.96      ( ~ v1_relat_1(sK6)
% 2.94/0.96      | ~ v1_relat_1(sK5)
% 2.94/0.96      | ~ v1_funct_1(sK6)
% 2.94/0.96      | ~ v1_funct_1(sK5)
% 2.94/0.96      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.94/0.96      | sK6 = sK5
% 2.94/0.96      | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_3144]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3613,plain,
% 2.94/0.96      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3144,c_33,c_31,c_30,c_28,c_1320,c_1323,c_1467,c_1788,
% 2.94/0.96                 c_2968,c_3160]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3617,plain,
% 2.94/0.96      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(superposition,[status(thm)],[c_1664,c_3613]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3618,plain,
% 2.94/0.96      ( sK4 = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3617,c_1742]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_24,plain,
% 2.94/0.96      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.94/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.94/0.96      inference(cnf_transformation,[],[f90]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_403,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.94/0.96      | sK6 != X0
% 2.94/0.96      | sK4 != X1
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_404,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 2.94/0.96      | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_403]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1082,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_10,plain,
% 2.94/0.96      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.94/0.96      inference(cnf_transformation,[],[f85]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1201,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_1082,c_10]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3630,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1201]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3637,plain,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1089]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_9,plain,
% 2.94/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.94/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3643,plain,
% 2.94/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3637,c_9]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3663,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(forward_subsumption_resolution,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3630,c_3643]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_21,plain,
% 2.94/0.96      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.94/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.94/0.96      | k1_xboole_0 = X1
% 2.94/0.96      | k1_xboole_0 = X0 ),
% 2.94/0.96      inference(cnf_transformation,[],[f88]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_383,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.94/0.96      | sK5 != X0
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | sK3 != X1
% 2.94/0.96      | k1_xboole_0 = X0
% 2.94/0.96      | k1_xboole_0 = X1 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_384,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | k1_xboole_0 = sK5
% 2.94/0.96      | k1_xboole_0 = sK3 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_383]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1083,plain,
% 2.94/0.96      ( sK4 != k1_xboole_0
% 2.94/0.96      | k1_xboole_0 = sK5
% 2.94/0.96      | k1_xboole_0 = sK3
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1208,plain,
% 2.94/0.96      ( sK5 = k1_xboole_0
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | sK3 = k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_1083,c_9]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3629,plain,
% 2.94/0.96      ( sK5 = k1_xboole_0
% 2.94/0.96      | sK3 = k1_xboole_0
% 2.94/0.96      | k1_xboole_0 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1208]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3666,plain,
% 2.94/0.96      ( sK5 = k1_xboole_0
% 2.94/0.96      | sK3 = k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(equality_resolution_simp,[status(thm)],[c_3629]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3638,plain,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1087]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3640,plain,
% 2.94/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3638,c_9]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3670,plain,
% 2.94/0.96      ( sK5 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.94/0.96      inference(forward_subsumption_resolution,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3666,c_3640]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_367,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.94/0.96      | sK6 != X0
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | sK3 != X1
% 2.94/0.96      | k1_xboole_0 = X0
% 2.94/0.96      | k1_xboole_0 = X1 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_368,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | k1_xboole_0 = sK6
% 2.94/0.96      | k1_xboole_0 = sK3 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_367]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1084,plain,
% 2.94/0.96      ( sK4 != k1_xboole_0
% 2.94/0.96      | k1_xboole_0 = sK6
% 2.94/0.96      | k1_xboole_0 = sK3
% 2.94/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1217,plain,
% 2.94/0.96      ( sK6 = k1_xboole_0
% 2.94/0.96      | sK4 != k1_xboole_0
% 2.94/0.96      | sK3 = k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_1084,c_9]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1355,plain,
% 2.94/0.96      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3935,plain,
% 2.94/0.96      ( sK3 = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3670,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,
% 2.94/0.96                 c_3640,c_3643]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4538,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3663,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,
% 2.94/0.96                 c_3640,c_3643]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3633,plain,
% 2.94/0.96      ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1481]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4036,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 2.94/0.96      inference(light_normalisation,[status(thm)],[c_3633,c_3935]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4541,plain,
% 2.94/0.96      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_4538,c_4036]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_416,plain,
% 2.94/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.94/0.96      | sK5 != X0
% 2.94/0.96      | sK4 != X1
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_417,plain,
% 2.94/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 2.94/0.96      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(unflattening,[status(thm)],[c_416]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1081,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 2.94/0.96      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1194,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_1081,c_10]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3631,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0
% 2.94/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1194]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3657,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.94/0.96      | sK3 != k1_xboole_0 ),
% 2.94/0.96      inference(forward_subsumption_resolution,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3631,c_3640]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4530,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.94/0.96      inference(global_propositional_subsumption,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_3657,c_28,c_1208,c_1217,c_1355,c_1742,c_2968,c_3617,
% 2.94/0.96                 c_3640,c_3643]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3632,plain,
% 2.94/0.96      ( k1_relset_1(sK3,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_3618,c_1482]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3996,plain,
% 2.94/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.94/0.96      inference(light_normalisation,[status(thm)],[c_3632,c_3935]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_4533,plain,
% 2.94/0.96      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.94/0.96      inference(demodulation,[status(thm)],[c_4530,c_3996]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1,plain,
% 2.94/0.96      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.94/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_3072,plain,
% 2.94/0.96      ( ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
% 2.94/0.96      | ~ v1_xboole_0(k1_relat_1(sK5)) ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_1]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1946,plain,
% 2.94/0.96      ( k1_relat_1(sK6) != X0
% 2.94/0.96      | k1_relat_1(sK6) = k1_relat_1(sK5)
% 2.94/0.96      | k1_relat_1(sK5) != X0 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_644]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1947,plain,
% 2.94/0.96      ( k1_relat_1(sK6) = k1_relat_1(sK5)
% 2.94/0.96      | k1_relat_1(sK6) != k1_xboole_0
% 2.94/0.96      | k1_relat_1(sK5) != k1_xboole_0 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_1946]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1428,plain,
% 2.94/0.96      ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
% 2.94/0.96      | ~ v1_relat_1(X0)
% 2.94/0.96      | ~ v1_relat_1(sK5)
% 2.94/0.96      | ~ v1_funct_1(X0)
% 2.94/0.96      | ~ v1_funct_1(sK5)
% 2.94/0.96      | X0 = sK5
% 2.94/0.96      | k1_relat_1(X0) != k1_relat_1(sK5) ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_1728,plain,
% 2.94/0.96      ( r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
% 2.94/0.96      | ~ v1_relat_1(sK6)
% 2.94/0.96      | ~ v1_relat_1(sK5)
% 2.94/0.96      | ~ v1_funct_1(sK6)
% 2.94/0.96      | ~ v1_funct_1(sK5)
% 2.94/0.96      | k1_relat_1(sK6) != k1_relat_1(sK5)
% 2.94/0.96      | sK6 = sK5 ),
% 2.94/0.96      inference(instantiation,[status(thm)],[c_1428]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(c_5,plain,
% 2.94/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 2.94/0.96      inference(cnf_transformation,[],[f53]) ).
% 2.94/0.96  
% 2.94/0.96  cnf(contradiction,plain,
% 2.94/0.96      ( $false ),
% 2.94/0.96      inference(minisat,
% 2.94/0.96                [status(thm)],
% 2.94/0.96                [c_4995,c_4541,c_4533,c_3072,c_2968,c_1947,c_1788,c_1728,
% 2.94/0.96                 c_1467,c_1323,c_1320,c_5,c_28,c_30,c_31,c_33]) ).
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/0.96  
% 2.94/0.96  ------                               Statistics
% 2.94/0.96  
% 2.94/0.96  ------ General
% 2.94/0.96  
% 2.94/0.96  abstr_ref_over_cycles:                  0
% 2.94/0.96  abstr_ref_under_cycles:                 0
% 2.94/0.96  gc_basic_clause_elim:                   0
% 2.94/0.96  forced_gc_time:                         0
% 2.94/0.96  parsing_time:                           0.01
% 2.94/0.96  unif_index_cands_time:                  0.
% 2.94/0.96  unif_index_add_time:                    0.
% 2.94/0.96  orderings_time:                         0.
% 2.94/0.96  out_proof_time:                         0.01
% 2.94/0.96  total_time:                             0.174
% 2.94/0.96  num_of_symbols:                         52
% 2.94/0.96  num_of_terms:                           4853
% 2.94/0.96  
% 2.94/0.96  ------ Preprocessing
% 2.94/0.96  
% 2.94/0.96  num_of_splits:                          0
% 2.94/0.96  num_of_split_atoms:                     0
% 2.94/0.96  num_of_reused_defs:                     0
% 2.94/0.96  num_eq_ax_congr_red:                    29
% 2.94/0.96  num_of_sem_filtered_clauses:            1
% 2.94/0.96  num_of_subtypes:                        0
% 2.94/0.96  monotx_restored_types:                  0
% 2.94/0.96  sat_num_of_epr_types:                   0
% 2.94/0.96  sat_num_of_non_cyclic_types:            0
% 2.94/0.96  sat_guarded_non_collapsed_types:        0
% 2.94/0.96  num_pure_diseq_elim:                    0
% 2.94/0.96  simp_replaced_by:                       0
% 2.94/0.96  res_preprocessed:                       144
% 2.94/0.96  prep_upred:                             0
% 2.94/0.96  prep_unflattend:                        37
% 2.94/0.96  smt_new_axioms:                         0
% 2.94/0.96  pred_elim_cands:                        6
% 2.94/0.96  pred_elim:                              2
% 2.94/0.96  pred_elim_cl:                           3
% 2.94/0.96  pred_elim_cycles:                       4
% 2.94/0.96  merged_defs:                            0
% 2.94/0.96  merged_defs_ncl:                        0
% 2.94/0.96  bin_hyper_res:                          0
% 2.94/0.96  prep_cycles:                            4
% 2.94/0.96  pred_elim_time:                         0.003
% 2.94/0.96  splitting_time:                         0.
% 2.94/0.96  sem_filter_time:                        0.
% 2.94/0.96  monotx_time:                            0.
% 2.94/0.96  subtype_inf_time:                       0.
% 2.94/0.96  
% 2.94/0.96  ------ Problem properties
% 2.94/0.96  
% 2.94/0.96  clauses:                                30
% 2.94/0.96  conjectures:                            5
% 2.94/0.96  epr:                                    7
% 2.94/0.96  horn:                                   22
% 2.94/0.96  ground:                                 11
% 2.94/0.96  unary:                                  9
% 2.94/0.96  binary:                                 10
% 2.94/0.96  lits:                                   72
% 2.94/0.96  lits_eq:                                28
% 2.94/0.96  fd_pure:                                0
% 2.94/0.96  fd_pseudo:                              0
% 2.94/0.96  fd_cond:                                1
% 2.94/0.96  fd_pseudo_cond:                         3
% 2.94/0.96  ac_symbols:                             0
% 2.94/0.96  
% 2.94/0.96  ------ Propositional Solver
% 2.94/0.96  
% 2.94/0.96  prop_solver_calls:                      29
% 2.94/0.96  prop_fast_solver_calls:                 1006
% 2.94/0.96  smt_solver_calls:                       0
% 2.94/0.96  smt_fast_solver_calls:                  0
% 2.94/0.96  prop_num_of_clauses:                    1730
% 2.94/0.96  prop_preprocess_simplified:             5580
% 2.94/0.96  prop_fo_subsumed:                       48
% 2.94/0.96  prop_solver_time:                       0.
% 2.94/0.96  smt_solver_time:                        0.
% 2.94/0.96  smt_fast_solver_time:                   0.
% 2.94/0.96  prop_fast_solver_time:                  0.
% 2.94/0.96  prop_unsat_core_time:                   0.
% 2.94/0.96  
% 2.94/0.96  ------ QBF
% 2.94/0.96  
% 2.94/0.96  qbf_q_res:                              0
% 2.94/0.96  qbf_num_tautologies:                    0
% 2.94/0.96  qbf_prep_cycles:                        0
% 2.94/0.96  
% 2.94/0.96  ------ BMC1
% 2.94/0.96  
% 2.94/0.96  bmc1_current_bound:                     -1
% 2.94/0.96  bmc1_last_solved_bound:                 -1
% 2.94/0.96  bmc1_unsat_core_size:                   -1
% 2.94/0.96  bmc1_unsat_core_parents_size:           -1
% 2.94/0.96  bmc1_merge_next_fun:                    0
% 2.94/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.94/0.96  
% 2.94/0.96  ------ Instantiation
% 2.94/0.96  
% 2.94/0.96  inst_num_of_clauses:                    643
% 2.94/0.96  inst_num_in_passive:                    291
% 2.94/0.96  inst_num_in_active:                     343
% 2.94/0.96  inst_num_in_unprocessed:                8
% 2.94/0.96  inst_num_of_loops:                      416
% 2.94/0.96  inst_num_of_learning_restarts:          0
% 2.94/0.96  inst_num_moves_active_passive:          68
% 2.94/0.96  inst_lit_activity:                      0
% 2.94/0.96  inst_lit_activity_moves:                0
% 2.94/0.96  inst_num_tautologies:                   0
% 2.94/0.96  inst_num_prop_implied:                  0
% 2.94/0.96  inst_num_existing_simplified:           0
% 2.94/0.96  inst_num_eq_res_simplified:             0
% 2.94/0.96  inst_num_child_elim:                    0
% 2.94/0.96  inst_num_of_dismatching_blockings:      212
% 2.94/0.96  inst_num_of_non_proper_insts:           716
% 2.94/0.96  inst_num_of_duplicates:                 0
% 2.94/0.96  inst_inst_num_from_inst_to_res:         0
% 2.94/0.96  inst_dismatching_checking_time:         0.
% 2.94/0.96  
% 2.94/0.96  ------ Resolution
% 2.94/0.96  
% 2.94/0.96  res_num_of_clauses:                     0
% 2.94/0.96  res_num_in_passive:                     0
% 2.94/0.96  res_num_in_active:                      0
% 2.94/0.96  res_num_of_loops:                       148
% 2.94/0.96  res_forward_subset_subsumed:            69
% 2.94/0.96  res_backward_subset_subsumed:           0
% 2.94/0.96  res_forward_subsumed:                   0
% 2.94/0.96  res_backward_subsumed:                  0
% 2.94/0.96  res_forward_subsumption_resolution:     0
% 2.94/0.96  res_backward_subsumption_resolution:    0
% 2.94/0.96  res_clause_to_clause_subsumption:       183
% 2.94/0.96  res_orphan_elimination:                 0
% 2.94/0.96  res_tautology_del:                      45
% 2.94/0.96  res_num_eq_res_simplified:              0
% 2.94/0.96  res_num_sel_changes:                    0
% 2.94/0.96  res_moves_from_active_to_pass:          0
% 2.94/0.96  
% 2.94/0.96  ------ Superposition
% 2.94/0.96  
% 2.94/0.96  sup_time_total:                         0.
% 2.94/0.96  sup_time_generating:                    0.
% 2.94/0.96  sup_time_sim_full:                      0.
% 2.94/0.96  sup_time_sim_immed:                     0.
% 2.94/0.96  
% 2.94/0.96  sup_num_of_clauses:                     65
% 2.94/0.96  sup_num_in_active:                      53
% 2.94/0.96  sup_num_in_passive:                     12
% 2.94/0.96  sup_num_of_loops:                       82
% 2.94/0.96  sup_fw_superposition:                   63
% 2.94/0.96  sup_bw_superposition:                   32
% 2.94/0.96  sup_immediate_simplified:               19
% 2.94/0.96  sup_given_eliminated:                   0
% 2.94/0.96  comparisons_done:                       0
% 2.94/0.96  comparisons_avoided:                    22
% 2.94/0.96  
% 2.94/0.96  ------ Simplifications
% 2.94/0.96  
% 2.94/0.96  
% 2.94/0.96  sim_fw_subset_subsumed:                 8
% 2.94/0.96  sim_bw_subset_subsumed:                 4
% 2.94/0.96  sim_fw_subsumed:                        5
% 2.94/0.96  sim_bw_subsumed:                        0
% 2.94/0.96  sim_fw_subsumption_res:                 4
% 2.94/0.96  sim_bw_subsumption_res:                 0
% 2.94/0.96  sim_tautology_del:                      2
% 2.94/0.96  sim_eq_tautology_del:                   15
% 2.94/0.96  sim_eq_res_simp:                        2
% 2.94/0.96  sim_fw_demodulated:                     7
% 2.94/0.96  sim_bw_demodulated:                     27
% 2.94/0.96  sim_light_normalised:                   3
% 2.94/0.96  sim_joinable_taut:                      0
% 2.94/0.96  sim_joinable_simp:                      0
% 2.94/0.96  sim_ac_normalised:                      0
% 2.94/0.96  sim_smt_subsumption:                    0
% 2.94/0.96  
%------------------------------------------------------------------------------
