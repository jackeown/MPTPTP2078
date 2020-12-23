%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:14 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  160 (8456 expanded)
%              Number of clauses        :  111 (2705 expanded)
%              Number of leaves         :   13 (2066 expanded)
%              Depth                    :   37
%              Number of atoms          :  585 (56342 expanded)
%              Number of equality atoms :  360 (14753 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f34,f33])).

fof(f57,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_326,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_327,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_664,plain,
    ( k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != sK5
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_327])).

cnf(c_665,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_940,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_665])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_362,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_363,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1425,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_363])).

cnf(c_2036,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_940,c_1425])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_384,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_749,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_384])).

cnf(c_750,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_939,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_750])).

cnf(c_419,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_420,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1428,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_420])).

cnf(c_1963,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_939,c_1428])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1225,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1966,plain,
    ( k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1963,c_1225])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1008,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1389,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_428,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_429,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1392,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_1396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_2219,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_25,c_1389,c_1396])).

cnf(c_2220,plain,
    ( k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2219])).

cnf(c_2231,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_2220])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_371,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_372,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1393,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1394,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_2245,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2231,c_28,c_1389,c_1394])).

cnf(c_2252,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_2245])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1224,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2638,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2252,c_1224])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1226,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2733,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2638,c_1226])).

cnf(c_2734,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2733])).

cnf(c_2778,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2733,c_24,c_21,c_1389,c_1393,c_1392,c_2734])).

cnf(c_2783,plain,
    ( k1_relat_1(sK4) != sK2
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2036,c_2778])).

cnf(c_2784,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2783,c_1963])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_320,plain,
    ( sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_19])).

cnf(c_2797,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2784,c_320])).

cnf(c_2870,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2797,c_1428])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_475,plain,
    ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_689,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != sK5
    | sK5 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_475])).

cnf(c_690,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_493,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_764,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_493])).

cnf(c_765,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_1009,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1415,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_1416,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1564,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_19,c_318,c_765,c_1416])).

cnf(c_2872,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2797,c_1564])).

cnf(c_2897,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2872])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_540,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_541,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_782,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_541])).

cnf(c_783,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_2873,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2797,c_783])).

cnf(c_2899,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2897,c_2873])).

cnf(c_2915,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2899])).

cnf(c_2926,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2870,c_2897,c_2915])).

cnf(c_2871,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2797,c_1425])).

cnf(c_510,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_511,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_720,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != sK5
    | sK3 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_511])).

cnf(c_721,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_2874,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2797,c_721])).

cnf(c_2900,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2897,c_2874])).

cnf(c_2912,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2900])).

cnf(c_2918,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2871,c_2897,c_2912])).

cnf(c_3031,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK5 = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_1225])).

cnf(c_3039,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK5 = X0
    | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3031,c_2918])).

cnf(c_3111,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_xboole_0
    | sK5 = X0
    | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3039,c_28,c_1389,c_1394])).

cnf(c_3112,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK5 = X0
    | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3111])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_3122,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK5 = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3112,c_1221])).

cnf(c_3132,plain,
    ( sK5 = sK4
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2926,c_3122])).

cnf(c_2824,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1772,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3132,c_2824,c_1772,c_1396,c_1389,c_318,c_19,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.99  
% 2.27/0.99  ------  iProver source info
% 2.27/0.99  
% 2.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.99  git: non_committed_changes: false
% 2.27/0.99  git: last_make_outside_of_git: false
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     num_symb
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       true
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  ------ Parsing...
% 2.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.99  ------ Proving...
% 2.27/0.99  ------ Problem Properties 
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  clauses                                 23
% 2.27/0.99  conjectures                             3
% 2.27/0.99  EPR                                     4
% 2.27/0.99  Horn                                    16
% 2.27/0.99  unary                                   4
% 2.27/0.99  binary                                  9
% 2.27/0.99  lits                                    68
% 2.27/0.99  lits eq                                 49
% 2.27/0.99  fd_pure                                 0
% 2.27/0.99  fd_pseudo                               0
% 2.27/0.99  fd_cond                                 0
% 2.27/0.99  fd_pseudo_cond                          2
% 2.27/0.99  AC symbols                              0
% 2.27/0.99  
% 2.27/0.99  ------ Schedule dynamic 5 is on 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  Current options:
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     none
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       false
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ Proving...
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS status Theorem for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  fof(f10,conjecture,(
% 2.27/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f11,negated_conjecture,(
% 2.27/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.27/0.99    inference(negated_conjecture,[],[f10])).
% 2.27/0.99  
% 2.27/0.99  fof(f25,plain,(
% 2.27/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.27/0.99    inference(ennf_transformation,[],[f11])).
% 2.27/0.99  
% 2.27/0.99  fof(f26,plain,(
% 2.27/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.27/0.99    inference(flattening,[],[f25])).
% 2.27/0.99  
% 2.27/0.99  fof(f34,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f33,plain,(
% 2.27/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f35,plain,(
% 2.27/0.99    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f34,f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f57,plain,(
% 2.27/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f9,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f23,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f9])).
% 2.27/0.99  
% 2.27/0.99  fof(f24,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(flattening,[],[f23])).
% 2.27/0.99  
% 2.27/0.99  fof(f32,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(nnf_transformation,[],[f24])).
% 2.27/0.99  
% 2.27/0.99  fof(f47,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f32])).
% 2.27/0.99  
% 2.27/0.99  fof(f58,plain,(
% 2.27/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f7,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f20,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f7])).
% 2.27/0.99  
% 2.27/0.99  fof(f44,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f20])).
% 2.27/0.99  
% 2.27/0.99  fof(f54,plain,(
% 2.27/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f55,plain,(
% 2.27/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f4,axiom,(
% 2.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f16,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.27/0.99    inference(ennf_transformation,[],[f4])).
% 2.27/0.99  
% 2.27/0.99  fof(f17,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(flattening,[],[f16])).
% 2.27/0.99  
% 2.27/0.99  fof(f29,plain,(
% 2.27/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f30,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f29])).
% 2.27/0.99  
% 2.27/0.99  fof(f40,plain,(
% 2.27/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f53,plain,(
% 2.27/0.99    v1_funct_1(sK4)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f6,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f19,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f6])).
% 2.27/0.99  
% 2.27/0.99  fof(f43,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f19])).
% 2.27/0.99  
% 2.27/0.99  fof(f56,plain,(
% 2.27/0.99    v1_funct_1(sK5)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f59,plain,(
% 2.27/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f41,plain,(
% 2.27/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f8,axiom,(
% 2.27/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f21,plain,(
% 2.27/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.27/0.99    inference(ennf_transformation,[],[f8])).
% 2.27/0.99  
% 2.27/0.99  fof(f22,plain,(
% 2.27/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(flattening,[],[f21])).
% 2.27/0.99  
% 2.27/0.99  fof(f31,plain,(
% 2.27/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(nnf_transformation,[],[f22])).
% 2.27/0.99  
% 2.27/0.99  fof(f46,plain,(
% 2.27/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f31])).
% 2.27/0.99  
% 2.27/0.99  fof(f61,plain,(
% 2.27/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(equality_resolution,[],[f46])).
% 2.27/0.99  
% 2.27/0.99  fof(f60,plain,(
% 2.27/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f51,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f32])).
% 2.27/0.99  
% 2.27/0.99  fof(f64,plain,(
% 2.27/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.27/0.99    inference(equality_resolution,[],[f51])).
% 2.27/0.99  
% 2.27/0.99  fof(f48,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f32])).
% 2.27/0.99  
% 2.27/0.99  fof(f66,plain,(
% 2.27/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.27/0.99    inference(equality_resolution,[],[f48])).
% 2.27/0.99  
% 2.27/0.99  fof(f1,axiom,(
% 2.27/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f13,plain,(
% 2.27/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.27/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.27/0.99  
% 2.27/0.99  fof(f14,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.27/0.99    inference(ennf_transformation,[],[f13])).
% 2.27/0.99  
% 2.27/0.99  fof(f36,plain,(
% 2.27/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f14])).
% 2.27/0.99  
% 2.27/0.99  fof(f3,axiom,(
% 2.27/0.99    v1_xboole_0(k1_xboole_0)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f39,plain,(
% 2.27/0.99    v1_xboole_0(k1_xboole_0)),
% 2.27/0.99    inference(cnf_transformation,[],[f3])).
% 2.27/0.99  
% 2.27/0.99  cnf(c_20,negated_conjecture,
% 2.27/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.27/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_16,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.27/0.99      | k1_xboole_0 = X2 ),
% 2.27/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_19,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_326,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.27/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != X0
% 2.27/0.99      | k1_xboole_0 = X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_327,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 2.27/0.99      | k1_relset_1(X0,X1,sK5) = X0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = X1 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_326]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_664,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,sK5) = X0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != sK5
% 2.27/0.99      | sK3 != X1
% 2.27/0.99      | sK2 != X0
% 2.27/0.99      | k1_xboole_0 = X1 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_327]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_665,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = sK3 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_664]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_940,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_665]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_8,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_362,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_363,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1425,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.27/0.99      inference(equality_resolution,[status(thm)],[c_363]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2036,plain,
% 2.27/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_940,c_1425]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_23,negated_conjecture,
% 2.27/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.27/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_22,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_383,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.27/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != X0
% 2.27/0.99      | k1_xboole_0 = X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_384,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.27/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = X1 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_383]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_749,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != sK4
% 2.27/0.99      | sK3 != X1
% 2.27/0.99      | sK2 != X0
% 2.27/0.99      | k1_xboole_0 = X1 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_384]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_750,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = sK3 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_749]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_939,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_750]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_419,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_420,plain,
% 2.27/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1428,plain,
% 2.27/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.27/0.99      inference(equality_resolution,[status(thm)],[c_420]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1963,plain,
% 2.27/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_939,c_1428]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_5,plain,
% 2.27/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0)
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | X0 = X1
% 2.27/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1225,plain,
% 2.27/0.99      ( X0 = X1
% 2.27/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.27/0.99      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_relat_1(X1) != iProver_top
% 2.27/0.99      | v1_funct_1(X1) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1966,plain,
% 2.27/0.99      ( k1_relat_1(X0) != sK2
% 2.27/0.99      | sK4 = X0
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_relat_1(sK4) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1963,c_1225]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_24,negated_conjecture,
% 2.27/0.99      ( v1_funct_1(sK4) ),
% 2.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_25,plain,
% 2.27/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1008,plain,( X0 = X0 ),theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1389,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1008]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_7,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | v1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_428,plain,
% 2.27/0.99      ( v1_relat_1(X0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_429,plain,
% 2.27/0.99      ( v1_relat_1(sK4)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1392,plain,
% 2.27/0.99      ( v1_relat_1(sK4)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_429]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1396,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2219,plain,
% 2.27/0.99      ( v1_funct_1(X0) != iProver_top
% 2.27/0.99      | k1_relat_1(X0) != sK2
% 2.27/0.99      | sK4 = X0
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_1966,c_25,c_1389,c_1396]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2220,plain,
% 2.27/0.99      ( k1_relat_1(X0) != sK2
% 2.27/0.99      | sK4 = X0
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.27/0.99      inference(renaming,[status(thm)],[c_2219]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2231,plain,
% 2.27/0.99      ( sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 2.27/0.99      | v1_relat_1(sK5) != iProver_top
% 2.27/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2036,c_2220]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_21,negated_conjecture,
% 2.27/0.99      ( v1_funct_1(sK5) ),
% 2.27/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_28,plain,
% 2.27/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_371,plain,
% 2.27/0.99      ( v1_relat_1(X0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_372,plain,
% 2.27/0.99      ( v1_relat_1(sK5)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1393,plain,
% 2.27/0.99      ( v1_relat_1(sK5)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_372]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1394,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2245,plain,
% 2.27/0.99      ( sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_2231,c_28,c_1389,c_1394]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2252,plain,
% 2.27/0.99      ( sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | r2_hidden(sK1(sK5,sK4),sK2) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2036,c_2245]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_18,negated_conjecture,
% 2.27/0.99      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1224,plain,
% 2.27/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.27/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2638,plain,
% 2.27/0.99      ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
% 2.27/0.99      | sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2252,c_1224]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_4,plain,
% 2.27/0.99      ( ~ v1_relat_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | X1 = X0
% 2.27/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.27/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1226,plain,
% 2.27/0.99      ( X0 = X1
% 2.27/0.99      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.27/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.27/0.99      | v1_relat_1(X1) != iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2733,plain,
% 2.27/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.27/0.99      | sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0
% 2.27/0.99      | v1_relat_1(sK5) != iProver_top
% 2.27/0.99      | v1_relat_1(sK4) != iProver_top
% 2.27/0.99      | v1_funct_1(sK5) != iProver_top
% 2.27/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2638,c_1226]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2734,plain,
% 2.27/0.99      ( ~ v1_relat_1(sK5)
% 2.27/0.99      | ~ v1_relat_1(sK4)
% 2.27/0.99      | ~ v1_funct_1(sK5)
% 2.27/0.99      | ~ v1_funct_1(sK4)
% 2.27/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.27/0.99      | sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2733]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2778,plain,
% 2.27/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.27/0.99      | sK5 = sK4
% 2.27/0.99      | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_2733,c_24,c_21,c_1389,c_1393,c_1392,c_2734]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2783,plain,
% 2.27/0.99      ( k1_relat_1(sK4) != sK2 | sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2036,c_2778]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2784,plain,
% 2.27/0.99      ( sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_2783,c_1963]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_9,plain,
% 2.27/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.27/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_17,negated_conjecture,
% 2.27/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.27/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_317,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | sK5 != X0
% 2.27/0.99      | sK4 != X0
% 2.27/0.99      | sK3 != X2
% 2.27/0.99      | sK2 != X1 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_318,plain,
% 2.27/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.27/0.99      | sK4 != sK5 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_320,plain,
% 2.27/0.99      ( sK4 != sK5 ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_318,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2797,plain,
% 2.27/0.99      ( sK3 = k1_xboole_0 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2784,c_320]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2870,plain,
% 2.27/0.99      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2797,c_1428]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_12,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.27/0.99      | k1_xboole_0 = X1
% 2.27/0.99      | k1_xboole_0 = X0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_474,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != X0
% 2.27/0.99      | k1_xboole_0 = X1
% 2.27/0.99      | k1_xboole_0 = X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_475,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = X0
% 2.27/0.99      | k1_xboole_0 = sK5 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_474]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_689,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != sK5
% 2.27/0.99      | sK5 = k1_xboole_0
% 2.27/0.99      | sK3 != k1_xboole_0
% 2.27/0.99      | sK2 != X0
% 2.27/0.99      | k1_xboole_0 = X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_475]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_690,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 = k1_xboole_0
% 2.27/0.99      | sK3 != k1_xboole_0
% 2.27/0.99      | k1_xboole_0 = sK2 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_689]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_492,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != X0
% 2.27/0.99      | k1_xboole_0 = X1
% 2.27/0.99      | k1_xboole_0 = X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_493,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | k1_xboole_0 = X0
% 2.27/0.99      | k1_xboole_0 = sK4 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_492]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_764,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != sK4
% 2.27/0.99      | sK4 = k1_xboole_0
% 2.27/0.99      | sK3 != k1_xboole_0
% 2.27/0.99      | sK2 != X0
% 2.27/0.99      | k1_xboole_0 = X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_493]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_765,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 = k1_xboole_0
% 2.27/0.99      | sK3 != k1_xboole_0
% 2.27/0.99      | k1_xboole_0 = sK2 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_764]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1009,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1415,plain,
% 2.27/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1009]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1416,plain,
% 2.27/0.99      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1415]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1564,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK3 != k1_xboole_0
% 2.27/0.99      | k1_xboole_0 = sK2 ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_690,c_19,c_318,c_765,c_1416]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2872,plain,
% 2.27/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))
% 2.27/0.99      | sK2 = k1_xboole_0
% 2.27/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2797,c_1564]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2897,plain,
% 2.27/0.99      ( sK2 = k1_xboole_0 ),
% 2.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_2872]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_15,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_540,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_541,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 2.27/0.99      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_540]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_782,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK4 != sK4
% 2.27/0.99      | sK3 != X0
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_541]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_783,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_782]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2873,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2797,c_783]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2899,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.27/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2897,c_2873]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2915,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_2899]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2926,plain,
% 2.27/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_2870,c_2897,c_2915]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2871,plain,
% 2.27/0.99      ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2797,c_1425]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_510,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_511,plain,
% 2.27/0.99      ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
% 2.27/0.99      | k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_720,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK5 != sK5
% 2.27/0.99      | sK3 != X0
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_511]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_721,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_720]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2874,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.27/0.99      | sK2 != k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2797,c_721]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2900,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.27/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2897,c_2874]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2912,plain,
% 2.27/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_2900]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2918,plain,
% 2.27/0.99      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_2871,c_2897,c_2912]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3031,plain,
% 2.27/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.27/0.99      | sK5 = X0
% 2.27/0.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_relat_1(sK5) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2918,c_1225]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3039,plain,
% 2.27/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.27/0.99      | sK5 = X0
% 2.27/0.99      | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_relat_1(sK5) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_3031,c_2918]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3111,plain,
% 2.27/0.99      ( v1_funct_1(X0) != iProver_top
% 2.27/0.99      | k1_relat_1(X0) != k1_xboole_0
% 2.27/0.99      | sK5 = X0
% 2.27/0.99      | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_3039,c_28,c_1389,c_1394]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3112,plain,
% 2.27/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.27/0.99      | sK5 = X0
% 2.27/0.99      | r2_hidden(sK1(sK5,X0),k1_xboole_0) = iProver_top
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.27/0.99      inference(renaming,[status(thm)],[c_3111]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_0,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3,plain,
% 2.27/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_280,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_281,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1221,plain,
% 2.27/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3122,plain,
% 2.27/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.27/0.99      | sK5 = X0
% 2.27/0.99      | v1_relat_1(X0) != iProver_top
% 2.27/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.27/0.99      inference(forward_subsumption_resolution,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_3112,c_1221]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3132,plain,
% 2.27/0.99      ( sK5 = sK4
% 2.27/0.99      | v1_relat_1(sK4) != iProver_top
% 2.27/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2926,c_3122]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2824,plain,
% 2.27/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1415]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1772,plain,
% 2.27/0.99      ( sK4 = sK4 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1008]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(contradiction,plain,
% 2.27/0.99      ( $false ),
% 2.27/0.99      inference(minisat,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_3132,c_2824,c_1772,c_1396,c_1389,c_318,c_19,c_25]) ).
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  ------                               Statistics
% 2.27/0.99  
% 2.27/0.99  ------ General
% 2.27/0.99  
% 2.27/0.99  abstr_ref_over_cycles:                  0
% 2.27/0.99  abstr_ref_under_cycles:                 0
% 2.27/0.99  gc_basic_clause_elim:                   0
% 2.27/0.99  forced_gc_time:                         0
% 2.27/0.99  parsing_time:                           0.01
% 2.27/0.99  unif_index_cands_time:                  0.
% 2.27/0.99  unif_index_add_time:                    0.
% 2.27/0.99  orderings_time:                         0.
% 2.27/0.99  out_proof_time:                         0.011
% 2.27/0.99  total_time:                             0.148
% 2.27/0.99  num_of_symbols:                         51
% 2.27/0.99  num_of_terms:                           2360
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing
% 2.27/0.99  
% 2.27/0.99  num_of_splits:                          0
% 2.27/0.99  num_of_split_atoms:                     0
% 2.27/0.99  num_of_reused_defs:                     0
% 2.27/0.99  num_eq_ax_congr_red:                    18
% 2.27/0.99  num_of_sem_filtered_clauses:            1
% 2.27/0.99  num_of_subtypes:                        0
% 2.27/0.99  monotx_restored_types:                  0
% 2.27/0.99  sat_num_of_epr_types:                   0
% 2.27/0.99  sat_num_of_non_cyclic_types:            0
% 2.27/0.99  sat_guarded_non_collapsed_types:        0
% 2.27/0.99  num_pure_diseq_elim:                    0
% 2.27/0.99  simp_replaced_by:                       0
% 2.27/0.99  res_preprocessed:                       115
% 2.27/0.99  prep_upred:                             0
% 2.27/0.99  prep_unflattend:                        96
% 2.27/0.99  smt_new_axioms:                         0
% 2.27/0.99  pred_elim_cands:                        3
% 2.27/0.99  pred_elim:                              5
% 2.27/0.99  pred_elim_cl:                           2
% 2.27/0.99  pred_elim_cycles:                       7
% 2.27/0.99  merged_defs:                            0
% 2.27/0.99  merged_defs_ncl:                        0
% 2.27/0.99  bin_hyper_res:                          0
% 2.27/0.99  prep_cycles:                            4
% 2.27/0.99  pred_elim_time:                         0.016
% 2.27/0.99  splitting_time:                         0.
% 2.27/0.99  sem_filter_time:                        0.
% 2.27/0.99  monotx_time:                            0.001
% 2.27/0.99  subtype_inf_time:                       0.
% 2.27/0.99  
% 2.27/0.99  ------ Problem properties
% 2.27/0.99  
% 2.27/0.99  clauses:                                23
% 2.27/0.99  conjectures:                            3
% 2.27/0.99  epr:                                    4
% 2.27/0.99  horn:                                   16
% 2.27/0.99  ground:                                 9
% 2.27/0.99  unary:                                  4
% 2.27/0.99  binary:                                 9
% 2.27/0.99  lits:                                   68
% 2.27/0.99  lits_eq:                                49
% 2.27/0.99  fd_pure:                                0
% 2.27/0.99  fd_pseudo:                              0
% 2.27/0.99  fd_cond:                                0
% 2.27/0.99  fd_pseudo_cond:                         2
% 2.27/0.99  ac_symbols:                             0
% 2.27/0.99  
% 2.27/0.99  ------ Propositional Solver
% 2.27/0.99  
% 2.27/0.99  prop_solver_calls:                      27
% 2.27/0.99  prop_fast_solver_calls:                 1027
% 2.27/0.99  smt_solver_calls:                       0
% 2.27/0.99  smt_fast_solver_calls:                  0
% 2.27/0.99  prop_num_of_clauses:                    779
% 2.27/0.99  prop_preprocess_simplified:             3314
% 2.27/0.99  prop_fo_subsumed:                       31
% 2.27/0.99  prop_solver_time:                       0.
% 2.27/0.99  smt_solver_time:                        0.
% 2.27/0.99  smt_fast_solver_time:                   0.
% 2.27/0.99  prop_fast_solver_time:                  0.
% 2.27/0.99  prop_unsat_core_time:                   0.
% 2.27/0.99  
% 2.27/0.99  ------ QBF
% 2.27/0.99  
% 2.27/0.99  qbf_q_res:                              0
% 2.27/0.99  qbf_num_tautologies:                    0
% 2.27/0.99  qbf_prep_cycles:                        0
% 2.27/0.99  
% 2.27/0.99  ------ BMC1
% 2.27/0.99  
% 2.27/0.99  bmc1_current_bound:                     -1
% 2.27/0.99  bmc1_last_solved_bound:                 -1
% 2.27/0.99  bmc1_unsat_core_size:                   -1
% 2.27/0.99  bmc1_unsat_core_parents_size:           -1
% 2.27/0.99  bmc1_merge_next_fun:                    0
% 2.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation
% 2.27/0.99  
% 2.27/0.99  inst_num_of_clauses:                    272
% 2.27/0.99  inst_num_in_passive:                    43
% 2.27/0.99  inst_num_in_active:                     190
% 2.27/0.99  inst_num_in_unprocessed:                39
% 2.27/0.99  inst_num_of_loops:                      230
% 2.27/0.99  inst_num_of_learning_restarts:          0
% 2.27/0.99  inst_num_moves_active_passive:          36
% 2.27/0.99  inst_lit_activity:                      0
% 2.27/0.99  inst_lit_activity_moves:                0
% 2.27/0.99  inst_num_tautologies:                   0
% 2.27/0.99  inst_num_prop_implied:                  0
% 2.27/0.99  inst_num_existing_simplified:           0
% 2.27/0.99  inst_num_eq_res_simplified:             0
% 2.27/0.99  inst_num_child_elim:                    0
% 2.27/0.99  inst_num_of_dismatching_blockings:      125
% 2.27/0.99  inst_num_of_non_proper_insts:           477
% 2.27/0.99  inst_num_of_duplicates:                 0
% 2.27/0.99  inst_inst_num_from_inst_to_res:         0
% 2.27/0.99  inst_dismatching_checking_time:         0.
% 2.27/0.99  
% 2.27/0.99  ------ Resolution
% 2.27/0.99  
% 2.27/0.99  res_num_of_clauses:                     0
% 2.27/0.99  res_num_in_passive:                     0
% 2.27/0.99  res_num_in_active:                      0
% 2.27/0.99  res_num_of_loops:                       119
% 2.27/0.99  res_forward_subset_subsumed:            52
% 2.27/0.99  res_backward_subset_subsumed:           4
% 2.27/0.99  res_forward_subsumed:                   7
% 2.27/0.99  res_backward_subsumed:                  3
% 2.27/0.99  res_forward_subsumption_resolution:     0
% 2.27/0.99  res_backward_subsumption_resolution:    0
% 2.27/0.99  res_clause_to_clause_subsumption:       229
% 2.27/0.99  res_orphan_elimination:                 0
% 2.27/0.99  res_tautology_del:                      70
% 2.27/0.99  res_num_eq_res_simplified:              2
% 2.27/0.99  res_num_sel_changes:                    0
% 2.27/0.99  res_moves_from_active_to_pass:          0
% 2.27/0.99  
% 2.27/0.99  ------ Superposition
% 2.27/0.99  
% 2.27/0.99  sup_time_total:                         0.
% 2.27/0.99  sup_time_generating:                    0.
% 2.27/0.99  sup_time_sim_full:                      0.
% 2.27/0.99  sup_time_sim_immed:                     0.
% 2.27/0.99  
% 2.27/0.99  sup_num_of_clauses:                     33
% 2.27/0.99  sup_num_in_active:                      18
% 2.27/0.99  sup_num_in_passive:                     15
% 2.27/0.99  sup_num_of_loops:                       45
% 2.27/0.99  sup_fw_superposition:                   19
% 2.27/0.99  sup_bw_superposition:                   28
% 2.27/0.99  sup_immediate_simplified:               31
% 2.27/0.99  sup_given_eliminated:                   1
% 2.27/0.99  comparisons_done:                       0
% 2.27/0.99  comparisons_avoided:                    27
% 2.27/0.99  
% 2.27/0.99  ------ Simplifications
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  sim_fw_subset_subsumed:                 15
% 2.27/0.99  sim_bw_subset_subsumed:                 4
% 2.27/0.99  sim_fw_subsumed:                        4
% 2.27/0.99  sim_bw_subsumed:                        2
% 2.27/0.99  sim_fw_subsumption_res:                 1
% 2.27/0.99  sim_bw_subsumption_res:                 0
% 2.27/0.99  sim_tautology_del:                      0
% 2.27/0.99  sim_eq_tautology_del:                   12
% 2.27/0.99  sim_eq_res_simp:                        3
% 2.27/0.99  sim_fw_demodulated:                     4
% 2.27/0.99  sim_bw_demodulated:                     31
% 2.27/0.99  sim_light_normalised:                   13
% 2.27/0.99  sim_joinable_taut:                      0
% 2.27/0.99  sim_joinable_simp:                      0
% 2.27/0.99  sim_ac_normalised:                      0
% 2.27/0.99  sim_smt_subsumption:                    0
% 2.27/0.99  
%------------------------------------------------------------------------------
