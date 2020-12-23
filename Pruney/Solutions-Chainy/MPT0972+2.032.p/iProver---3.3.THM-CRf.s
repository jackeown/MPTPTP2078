%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:14 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  161 (8414 expanded)
%              Number of clauses        :  103 (2454 expanded)
%              Number of leaves         :   16 (2123 expanded)
%              Depth                    :   28
%              Number of atoms          :  559 (55950 expanded)
%              Number of equality atoms :  315 (13612 expanded)
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

fof(f65,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f81,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
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
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
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

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_573,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_575,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_28])).

cnf(c_1508,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1510,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1887,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1508,c_1510])).

cnf(c_1965,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_575,c_1887])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_584,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_586,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_31])).

cnf(c_1506,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1888,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1506,c_1510])).

cnf(c_2036,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_586,c_1888])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1512,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2629,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1512])).

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

cnf(c_1750,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1751,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1750])).

cnf(c_3139,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2629,c_37,c_39,c_1751])).

cnf(c_3140,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3139])).

cnf(c_3152,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_3140])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_422,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1753,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1754,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_913,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1771,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_2184,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_912,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2793,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_3281,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3152,c_34,c_36,c_28,c_422,c_1754,c_2184,c_2793])).

cnf(c_3287,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_3281])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1509,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3303,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3287,c_1509])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1513,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3420,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_1513])).

cnf(c_3436,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3420])).

cnf(c_4115,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3420,c_33,c_31,c_30,c_28,c_422,c_1750,c_1753,c_2184,c_2793,c_3436])).

cnf(c_4119,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1965,c_4115])).

cnf(c_4207,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4119,c_2036])).

cnf(c_4226,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4207,c_1508])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4232,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4226,c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1931,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1510])).

cnf(c_4497,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4232,c_1931])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK6 != X0
    | sK4 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_547,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_1502,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_1618,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1502,c_8])).

cnf(c_4220,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4207,c_1618])).

cnf(c_4247,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4220,c_4232])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_527,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_1503,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1625,plain,
    ( sK5 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1503,c_7])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK6 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_1504,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1634,plain,
    ( sK6 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1504,c_7])).

cnf(c_1772,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_4227,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4207,c_1506])).

cnf(c_4229,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4227,c_7])).

cnf(c_5156,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4247,c_28,c_422,c_1625,c_1634,c_1772,c_2036,c_4119,c_4229,c_4232])).

cnf(c_5159,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4497,c_5156])).

cnf(c_4311,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4229,c_1931])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK5 != X0
    | sK4 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_560,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1501,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1611,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1501,c_8])).

cnf(c_4221,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4207,c_1611])).

cnf(c_4241,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4221,c_4229])).

cnf(c_5149,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4241,c_28,c_422,c_1625,c_1634,c_1772,c_2036,c_4119,c_4229,c_4232])).

cnf(c_5152,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4311,c_5149])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2548,plain,
    ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ v1_xboole_0(k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_914,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2048,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK6))
    | k1_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_2050,plain,
    ( v1_xboole_0(k1_relat_1(sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_1898,plain,
    ( k1_relat_1(sK6) != X0
    | k1_relat_1(sK5) != X0
    | k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_1899,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k1_relat_1(sK5) = k1_relat_1(sK6)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_1794,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5159,c_5152,c_2548,c_2050,c_1899,c_1794,c_1753,c_1750,c_422,c_5,c_28,c_30,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.88/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.99  
% 2.88/0.99  ------  iProver source info
% 2.88/0.99  
% 2.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.99  git: non_committed_changes: false
% 2.88/0.99  git: last_make_outside_of_git: false
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     num_symb
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       true
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  ------ Parsing...
% 2.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.99  ------ Proving...
% 2.88/0.99  ------ Problem Properties 
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  clauses                                 30
% 2.88/0.99  conjectures                             5
% 2.88/0.99  EPR                                     7
% 2.88/0.99  Horn                                    22
% 2.88/0.99  unary                                   9
% 2.88/0.99  binary                                  11
% 2.88/0.99  lits                                    71
% 2.88/0.99  lits eq                                 28
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 1
% 2.88/0.99  fd_pseudo_cond                          3
% 2.88/0.99  AC symbols                              0
% 2.88/0.99  
% 2.88/0.99  ------ Schedule dynamic 5 is on 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  Current options:
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     none
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       false
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ Proving...
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS status Theorem for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  fof(f13,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f26,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f13])).
% 2.88/0.99  
% 2.88/0.99  fof(f27,plain,(
% 2.88/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(flattening,[],[f26])).
% 2.88/0.99  
% 2.88/0.99  fof(f44,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(nnf_transformation,[],[f27])).
% 2.88/0.99  
% 2.88/0.99  fof(f68,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f44])).
% 2.88/0.99  
% 2.88/0.99  fof(f14,conjecture,(
% 2.88/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f15,negated_conjecture,(
% 2.88/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.88/0.99    inference(negated_conjecture,[],[f14])).
% 2.88/0.99  
% 2.88/0.99  fof(f28,plain,(
% 2.88/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.88/0.99    inference(ennf_transformation,[],[f15])).
% 2.88/0.99  
% 2.88/0.99  fof(f29,plain,(
% 2.88/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.88/0.99    inference(flattening,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f46,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f45,plain,(
% 2.88/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f47,plain,(
% 2.88/0.99    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f29,f46,f45])).
% 2.88/0.99  
% 2.88/0.99  fof(f78,plain,(
% 2.88/0.99    v1_funct_2(sK6,sK3,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f79,plain,(
% 2.88/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f11,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f23,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f65,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f75,plain,(
% 2.88/0.99    v1_funct_2(sK5,sK3,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f76,plain,(
% 2.88/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f9,axiom,(
% 2.88/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f20,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f9])).
% 2.88/0.99  
% 2.88/0.99  fof(f21,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.99    inference(flattening,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f41,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f42,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).
% 2.88/0.99  
% 2.88/0.99  fof(f62,plain,(
% 2.88/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f42])).
% 2.88/0.99  
% 2.88/0.99  fof(f77,plain,(
% 2.88/0.99    v1_funct_1(sK6)),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f10,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f22,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f10])).
% 2.88/0.99  
% 2.88/0.99  fof(f64,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f22])).
% 2.88/0.99  
% 2.88/0.99  fof(f74,plain,(
% 2.88/0.99    v1_funct_1(sK5)),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f12,axiom,(
% 2.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f24,plain,(
% 2.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.88/0.99    inference(ennf_transformation,[],[f12])).
% 2.88/0.99  
% 2.88/0.99  fof(f25,plain,(
% 2.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(flattening,[],[f24])).
% 2.88/0.99  
% 2.88/0.99  fof(f43,plain,(
% 2.88/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(nnf_transformation,[],[f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f67,plain,(
% 2.88/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f43])).
% 2.88/0.99  
% 2.88/0.99  fof(f84,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(equality_resolution,[],[f67])).
% 2.88/0.99  
% 2.88/0.99  fof(f81,plain,(
% 2.88/0.99    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f80,plain,(
% 2.88/0.99    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f47])).
% 2.88/0.99  
% 2.88/0.99  fof(f63,plain,(
% 2.88/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f42])).
% 2.88/0.99  
% 2.88/0.99  fof(f5,axiom,(
% 2.88/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f38,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.88/0.99    inference(nnf_transformation,[],[f5])).
% 2.88/0.99  
% 2.88/0.99  fof(f39,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.88/0.99    inference(flattening,[],[f38])).
% 2.88/0.99  
% 2.88/0.99  fof(f57,plain,(
% 2.88/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.88/0.99    inference(cnf_transformation,[],[f39])).
% 2.88/0.99  
% 2.88/0.99  fof(f82,plain,(
% 2.88/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.88/0.99    inference(equality_resolution,[],[f57])).
% 2.88/0.99  
% 2.88/0.99  fof(f56,plain,(
% 2.88/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f39])).
% 2.88/0.99  
% 2.88/0.99  fof(f83,plain,(
% 2.88/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.88/0.99    inference(equality_resolution,[],[f56])).
% 2.88/0.99  
% 2.88/0.99  fof(f69,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f44])).
% 2.88/0.99  
% 2.88/0.99  fof(f89,plain,(
% 2.88/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.88/0.99    inference(equality_resolution,[],[f69])).
% 2.88/0.99  
% 2.88/0.99  fof(f72,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f44])).
% 2.88/0.99  
% 2.88/0.99  fof(f87,plain,(
% 2.88/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.88/0.99    inference(equality_resolution,[],[f72])).
% 2.88/0.99  
% 2.88/0.99  fof(f1,axiom,(
% 2.88/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f30,plain,(
% 2.88/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.88/0.99    inference(nnf_transformation,[],[f1])).
% 2.88/0.99  
% 2.88/0.99  fof(f31,plain,(
% 2.88/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.88/0.99    inference(rectify,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f32,plain,(
% 2.88/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f33,plain,(
% 2.88/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f48,plain,(
% 2.88/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f33])).
% 2.88/0.99  
% 2.88/0.99  fof(f3,axiom,(
% 2.88/0.99    v1_xboole_0(k1_xboole_0)),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f53,plain,(
% 2.88/0.99    v1_xboole_0(k1_xboole_0)),
% 2.88/0.99    inference(cnf_transformation,[],[f3])).
% 2.88/0.99  
% 2.88/0.99  cnf(c_25,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_29,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_572,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | sK6 != X0
% 2.88/0.99      | sK4 != X2
% 2.88/0.99      | sK3 != X1
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_573,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.88/0.99      | k1_relset_1(sK3,sK4,sK6) = sK3
% 2.88/0.99      | k1_xboole_0 = sK4 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_572]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_28,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_575,plain,
% 2.88/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_573,c_28]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1508,plain,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_17,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1510,plain,
% 2.88/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1887,plain,
% 2.88/0.99      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1508,c_1510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1965,plain,
% 2.88/0.99      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_575,c_1887]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_32,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_583,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | sK5 != X0
% 2.88/0.99      | sK4 != X2
% 2.88/0.99      | sK3 != X1
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_584,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.88/0.99      | k1_relset_1(sK3,sK4,sK5) = sK3
% 2.88/0.99      | k1_xboole_0 = sK4 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_583]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_31,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_586,plain,
% 2.88/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_584,c_31]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1506,plain,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1888,plain,
% 2.88/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1506,c_1510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2036,plain,
% 2.88/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_586,c_1888]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_15,plain,
% 2.88/0.99      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | X1 = X0
% 2.88/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1512,plain,
% 2.88/0.99      ( X0 = X1
% 2.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.88/0.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.88/0.99      | v1_relat_1(X1) != iProver_top
% 2.88/0.99      | v1_relat_1(X0) != iProver_top
% 2.88/0.99      | v1_funct_1(X0) != iProver_top
% 2.88/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2629,plain,
% 2.88/0.99      ( k1_relat_1(X0) != sK3
% 2.88/0.99      | sK6 = X0
% 2.88/0.99      | sK4 = k1_xboole_0
% 2.88/0.99      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.88/0.99      | v1_relat_1(X0) != iProver_top
% 2.88/0.99      | v1_relat_1(sK6) != iProver_top
% 2.88/0.99      | v1_funct_1(X0) != iProver_top
% 2.88/0.99      | v1_funct_1(sK6) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1965,c_1512]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_30,negated_conjecture,
% 2.88/0.99      ( v1_funct_1(sK6) ),
% 2.88/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_37,plain,
% 2.88/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_39,plain,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_16,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | v1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1750,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.88/0.99      | v1_relat_1(sK6) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1751,plain,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.88/0.99      | v1_relat_1(sK6) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1750]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3139,plain,
% 2.88/0.99      ( v1_funct_1(X0) != iProver_top
% 2.88/0.99      | k1_relat_1(X0) != sK3
% 2.88/0.99      | sK6 = X0
% 2.88/0.99      | sK4 = k1_xboole_0
% 2.88/0.99      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2629,c_37,c_39,c_1751]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3140,plain,
% 2.88/0.99      ( k1_relat_1(X0) != sK3
% 2.88/0.99      | sK6 = X0
% 2.88/0.99      | sK4 = k1_xboole_0
% 2.88/0.99      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.88/0.99      | v1_relat_1(X0) != iProver_top
% 2.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_3139]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3152,plain,
% 2.88/0.99      ( sK6 = sK5
% 2.88/0.99      | sK4 = k1_xboole_0
% 2.88/0.99      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.88/0.99      | v1_relat_1(sK5) != iProver_top
% 2.88/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2036,c_3140]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_33,negated_conjecture,
% 2.88/0.99      ( v1_funct_1(sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_34,plain,
% 2.88/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_36,plain,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_18,plain,
% 2.88/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_26,negated_conjecture,
% 2.88/0.99      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 2.88/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_421,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | sK6 != X0
% 2.88/0.99      | sK5 != X0
% 2.88/0.99      | sK4 != X2
% 2.88/0.99      | sK3 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_422,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.88/0.99      | sK5 != sK6 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1753,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.88/0.99      | v1_relat_1(sK5) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1754,plain,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.88/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1753]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_913,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1771,plain,
% 2.88/0.99      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_913]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2184,plain,
% 2.88/0.99      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1771]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_912,plain,( X0 = X0 ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2793,plain,
% 2.88/0.99      ( sK5 = sK5 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_912]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3281,plain,
% 2.88/0.99      ( sK4 = k1_xboole_0
% 2.88/0.99      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_3152,c_34,c_36,c_28,c_422,c_1754,c_2184,c_2793]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3287,plain,
% 2.88/0.99      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2036,c_3281]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_27,negated_conjecture,
% 2.88/0.99      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1509,plain,
% 2.88/0.99      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 2.88/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3303,plain,
% 2.88/0.99      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.88/0.99      | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3287,c_1509]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_14,plain,
% 2.88/0.99      ( ~ v1_relat_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | X0 = X1
% 2.88/0.99      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1513,plain,
% 2.88/0.99      ( X0 = X1
% 2.88/0.99      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.88/0.99      | v1_relat_1(X0) != iProver_top
% 2.88/0.99      | v1_relat_1(X1) != iProver_top
% 2.88/0.99      | v1_funct_1(X1) != iProver_top
% 2.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3420,plain,
% 2.88/0.99      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.88/0.99      | sK6 = sK5
% 2.88/0.99      | sK4 = k1_xboole_0
% 2.88/0.99      | v1_relat_1(sK6) != iProver_top
% 2.88/0.99      | v1_relat_1(sK5) != iProver_top
% 2.88/0.99      | v1_funct_1(sK6) != iProver_top
% 2.88/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3303,c_1513]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3436,plain,
% 2.88/0.99      ( ~ v1_relat_1(sK6)
% 2.88/0.99      | ~ v1_relat_1(sK5)
% 2.88/0.99      | ~ v1_funct_1(sK6)
% 2.88/0.99      | ~ v1_funct_1(sK5)
% 2.88/0.99      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.88/0.99      | sK6 = sK5
% 2.88/0.99      | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3420]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4115,plain,
% 2.88/0.99      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_3420,c_33,c_31,c_30,c_28,c_422,c_1750,c_1753,c_2184,
% 2.88/0.99                 c_2793,c_3436]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4119,plain,
% 2.88/0.99      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1965,c_4115]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4207,plain,
% 2.88/0.99      ( sK4 = k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4119,c_2036]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4226,plain,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4207,c_1508]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7,plain,
% 2.88/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4232,plain,
% 2.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4226,c_7]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8,plain,
% 2.88/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1931,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.88/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8,c_1510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4497,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4232,c_1931]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_24,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_546,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.88/0.99      | sK6 != X0
% 2.88/0.99      | sK4 != X1
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_547,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1502,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1618,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_1502,c_8]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4220,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4207,c_1618]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4247,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(forward_subsumption_resolution,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4220,c_4232]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_21,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.88/0.99      | k1_xboole_0 = X1
% 2.88/0.99      | k1_xboole_0 = X0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_526,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.88/0.99      | sK5 != X0
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | sK3 != X1
% 2.88/0.99      | k1_xboole_0 = X0
% 2.88/0.99      | k1_xboole_0 = X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_527,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK5
% 2.88/0.99      | k1_xboole_0 = sK3 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1503,plain,
% 2.88/0.99      ( sK4 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK5
% 2.88/0.99      | k1_xboole_0 = sK3
% 2.88/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1625,plain,
% 2.88/0.99      ( sK5 = k1_xboole_0
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | sK3 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_1503,c_7]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_510,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.88/0.99      | sK6 != X0
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | sK3 != X1
% 2.88/0.99      | k1_xboole_0 = X0
% 2.88/0.99      | k1_xboole_0 = X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_511,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK6
% 2.88/0.99      | k1_xboole_0 = sK3 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1504,plain,
% 2.88/0.99      ( sK4 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK6
% 2.88/0.99      | k1_xboole_0 = sK3
% 2.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1634,plain,
% 2.88/0.99      ( sK6 = k1_xboole_0
% 2.88/0.99      | sK4 != k1_xboole_0
% 2.88/0.99      | sK3 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_1504,c_7]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1772,plain,
% 2.88/0.99      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1771]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4227,plain,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4207,c_1506]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4229,plain,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4227,c_7]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5156,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4247,c_28,c_422,c_1625,c_1634,c_1772,c_2036,c_4119,
% 2.88/0.99                 c_4229,c_4232]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5159,plain,
% 2.88/0.99      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4497,c_5156]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4311,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4229,c_1931]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_559,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.88/0.99      | sK5 != X0
% 2.88/0.99      | sK4 != X1
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_560,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_559]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1501,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1611,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_1501,c_8]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4221,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_4207,c_1611]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4241,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.88/0.99      | sK3 != k1_xboole_0 ),
% 2.88/0.99      inference(forward_subsumption_resolution,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4221,c_4229]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5149,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4241,c_28,c_422,c_1625,c_1634,c_1772,c_2036,c_4119,
% 2.88/0.99                 c_4229,c_4232]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5152,plain,
% 2.88/0.99      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4311,c_5149]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2548,plain,
% 2.88/0.99      ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 2.88/0.99      | ~ v1_xboole_0(k1_relat_1(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_914,plain,
% 2.88/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.88/0.99      theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2048,plain,
% 2.88/0.99      ( ~ v1_xboole_0(X0)
% 2.88/0.99      | v1_xboole_0(k1_relat_1(sK6))
% 2.88/0.99      | k1_relat_1(sK6) != X0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_914]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2050,plain,
% 2.88/0.99      ( v1_xboole_0(k1_relat_1(sK6))
% 2.88/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.88/0.99      | k1_relat_1(sK6) != k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2048]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1898,plain,
% 2.88/0.99      ( k1_relat_1(sK6) != X0
% 2.88/0.99      | k1_relat_1(sK5) != X0
% 2.88/0.99      | k1_relat_1(sK5) = k1_relat_1(sK6) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_913]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1899,plain,
% 2.88/0.99      ( k1_relat_1(sK6) != k1_xboole_0
% 2.88/0.99      | k1_relat_1(sK5) = k1_relat_1(sK6)
% 2.88/0.99      | k1_relat_1(sK5) != k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1898]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1794,plain,
% 2.88/0.99      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 2.88/0.99      | ~ v1_relat_1(sK6)
% 2.88/0.99      | ~ v1_relat_1(sK5)
% 2.88/0.99      | ~ v1_funct_1(sK6)
% 2.88/0.99      | ~ v1_funct_1(sK5)
% 2.88/0.99      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.88/0.99      | sK5 = sK6 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5,plain,
% 2.88/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(contradiction,plain,
% 2.88/0.99      ( $false ),
% 2.88/0.99      inference(minisat,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_5159,c_5152,c_2548,c_2050,c_1899,c_1794,c_1753,c_1750,
% 2.88/0.99                 c_422,c_5,c_28,c_30,c_31,c_33]) ).
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  ------                               Statistics
% 2.88/0.99  
% 2.88/0.99  ------ General
% 2.88/0.99  
% 2.88/0.99  abstr_ref_over_cycles:                  0
% 2.88/0.99  abstr_ref_under_cycles:                 0
% 2.88/0.99  gc_basic_clause_elim:                   0
% 2.88/0.99  forced_gc_time:                         0
% 2.88/0.99  parsing_time:                           0.009
% 2.88/0.99  unif_index_cands_time:                  0.
% 2.88/0.99  unif_index_add_time:                    0.
% 2.88/0.99  orderings_time:                         0.
% 2.88/0.99  out_proof_time:                         0.009
% 2.88/0.99  total_time:                             0.162
% 2.88/0.99  num_of_symbols:                         52
% 2.88/0.99  num_of_terms:                           3396
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing
% 2.88/0.99  
% 2.88/0.99  num_of_splits:                          0
% 2.88/0.99  num_of_split_atoms:                     0
% 2.88/0.99  num_of_reused_defs:                     0
% 2.88/0.99  num_eq_ax_congr_red:                    29
% 2.88/0.99  num_of_sem_filtered_clauses:            1
% 2.88/0.99  num_of_subtypes:                        0
% 2.88/0.99  monotx_restored_types:                  0
% 2.88/0.99  sat_num_of_epr_types:                   0
% 2.88/0.99  sat_num_of_non_cyclic_types:            0
% 2.88/0.99  sat_guarded_non_collapsed_types:        0
% 2.88/0.99  num_pure_diseq_elim:                    0
% 2.88/0.99  simp_replaced_by:                       0
% 2.88/0.99  res_preprocessed:                       145
% 2.88/0.99  prep_upred:                             0
% 2.88/0.99  prep_unflattend:                        41
% 2.88/0.99  smt_new_axioms:                         0
% 2.88/0.99  pred_elim_cands:                        6
% 2.88/0.99  pred_elim:                              2
% 2.88/0.99  pred_elim_cl:                           4
% 2.88/0.99  pred_elim_cycles:                       5
% 2.88/0.99  merged_defs:                            8
% 2.88/0.99  merged_defs_ncl:                        0
% 2.88/0.99  bin_hyper_res:                          8
% 2.88/0.99  prep_cycles:                            4
% 2.88/0.99  pred_elim_time:                         0.007
% 2.88/0.99  splitting_time:                         0.
% 2.88/0.99  sem_filter_time:                        0.
% 2.88/0.99  monotx_time:                            0.001
% 2.88/0.99  subtype_inf_time:                       0.
% 2.88/0.99  
% 2.88/0.99  ------ Problem properties
% 2.88/0.99  
% 2.88/0.99  clauses:                                30
% 2.88/0.99  conjectures:                            5
% 2.88/0.99  epr:                                    7
% 2.88/0.99  horn:                                   22
% 2.88/0.99  ground:                                 12
% 2.88/0.99  unary:                                  9
% 2.88/0.99  binary:                                 11
% 2.88/0.99  lits:                                   71
% 2.88/0.99  lits_eq:                                28
% 2.88/0.99  fd_pure:                                0
% 2.88/0.99  fd_pseudo:                              0
% 2.88/0.99  fd_cond:                                1
% 2.88/0.99  fd_pseudo_cond:                         3
% 2.88/0.99  ac_symbols:                             0
% 2.88/0.99  
% 2.88/0.99  ------ Propositional Solver
% 2.88/0.99  
% 2.88/0.99  prop_solver_calls:                      28
% 2.88/0.99  prop_fast_solver_calls:                 965
% 2.88/0.99  smt_solver_calls:                       0
% 2.88/0.99  smt_fast_solver_calls:                  0
% 2.88/0.99  prop_num_of_clauses:                    1482
% 2.88/0.99  prop_preprocess_simplified:             5393
% 2.88/0.99  prop_fo_subsumed:                       37
% 2.88/0.99  prop_solver_time:                       0.
% 2.88/0.99  smt_solver_time:                        0.
% 2.88/0.99  smt_fast_solver_time:                   0.
% 2.88/0.99  prop_fast_solver_time:                  0.
% 2.88/0.99  prop_unsat_core_time:                   0.
% 2.88/0.99  
% 2.88/0.99  ------ QBF
% 2.88/0.99  
% 2.88/0.99  qbf_q_res:                              0
% 2.88/0.99  qbf_num_tautologies:                    0
% 2.88/0.99  qbf_prep_cycles:                        0
% 2.88/0.99  
% 2.88/0.99  ------ BMC1
% 2.88/0.99  
% 2.88/0.99  bmc1_current_bound:                     -1
% 2.88/0.99  bmc1_last_solved_bound:                 -1
% 2.88/0.99  bmc1_unsat_core_size:                   -1
% 2.88/0.99  bmc1_unsat_core_parents_size:           -1
% 2.88/0.99  bmc1_merge_next_fun:                    0
% 2.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation
% 2.88/0.99  
% 2.88/0.99  inst_num_of_clauses:                    439
% 2.88/0.99  inst_num_in_passive:                    119
% 2.88/0.99  inst_num_in_active:                     249
% 2.88/0.99  inst_num_in_unprocessed:                71
% 2.88/0.99  inst_num_of_loops:                      380
% 2.88/0.99  inst_num_of_learning_restarts:          0
% 2.88/0.99  inst_num_moves_active_passive:          128
% 2.88/0.99  inst_lit_activity:                      0
% 2.88/0.99  inst_lit_activity_moves:                0
% 2.88/0.99  inst_num_tautologies:                   0
% 2.88/0.99  inst_num_prop_implied:                  0
% 2.88/0.99  inst_num_existing_simplified:           0
% 2.88/0.99  inst_num_eq_res_simplified:             0
% 2.88/0.99  inst_num_child_elim:                    0
% 2.88/0.99  inst_num_of_dismatching_blockings:      110
% 2.88/0.99  inst_num_of_non_proper_insts:           592
% 2.88/0.99  inst_num_of_duplicates:                 0
% 2.88/0.99  inst_inst_num_from_inst_to_res:         0
% 2.88/0.99  inst_dismatching_checking_time:         0.
% 2.88/0.99  
% 2.88/0.99  ------ Resolution
% 2.88/0.99  
% 2.88/0.99  res_num_of_clauses:                     0
% 2.88/0.99  res_num_in_passive:                     0
% 2.88/0.99  res_num_in_active:                      0
% 2.88/0.99  res_num_of_loops:                       149
% 2.88/0.99  res_forward_subset_subsumed:            65
% 2.88/0.99  res_backward_subset_subsumed:           0
% 2.88/0.99  res_forward_subsumed:                   0
% 2.88/0.99  res_backward_subsumed:                  0
% 2.88/0.99  res_forward_subsumption_resolution:     0
% 2.88/0.99  res_backward_subsumption_resolution:    0
% 2.88/0.99  res_clause_to_clause_subsumption:       202
% 2.88/0.99  res_orphan_elimination:                 0
% 2.88/0.99  res_tautology_del:                      84
% 2.88/0.99  res_num_eq_res_simplified:              0
% 2.88/0.99  res_num_sel_changes:                    0
% 2.88/0.99  res_moves_from_active_to_pass:          0
% 2.88/0.99  
% 2.88/0.99  ------ Superposition
% 2.88/0.99  
% 2.88/0.99  sup_time_total:                         0.
% 2.88/0.99  sup_time_generating:                    0.
% 2.88/0.99  sup_time_sim_full:                      0.
% 2.88/0.99  sup_time_sim_immed:                     0.
% 2.88/0.99  
% 2.88/0.99  sup_num_of_clauses:                     88
% 2.88/0.99  sup_num_in_active:                      56
% 2.88/0.99  sup_num_in_passive:                     32
% 2.88/0.99  sup_num_of_loops:                       75
% 2.88/0.99  sup_fw_superposition:                   58
% 2.88/0.99  sup_bw_superposition:                   38
% 2.88/0.99  sup_immediate_simplified:               14
% 2.88/0.99  sup_given_eliminated:                   0
% 2.88/0.99  comparisons_done:                       0
% 2.88/0.99  comparisons_avoided:                    10
% 2.88/0.99  
% 2.88/0.99  ------ Simplifications
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  sim_fw_subset_subsumed:                 0
% 2.88/0.99  sim_bw_subset_subsumed:                 4
% 2.88/0.99  sim_fw_subsumed:                        2
% 2.88/0.99  sim_bw_subsumed:                        0
% 2.88/0.99  sim_fw_subsumption_res:                 4
% 2.88/0.99  sim_bw_subsumption_res:                 0
% 2.88/0.99  sim_tautology_del:                      2
% 2.88/0.99  sim_eq_tautology_del:                   9
% 2.88/0.99  sim_eq_res_simp:                        2
% 2.88/0.99  sim_fw_demodulated:                     12
% 2.88/0.99  sim_bw_demodulated:                     18
% 2.88/0.99  sim_light_normalised:                   0
% 2.88/0.99  sim_joinable_taut:                      0
% 2.88/0.99  sim_joinable_simp:                      0
% 2.88/0.99  sim_ac_normalised:                      0
% 2.88/0.99  sim_smt_subsumption:                    0
% 2.88/0.99  
%------------------------------------------------------------------------------
