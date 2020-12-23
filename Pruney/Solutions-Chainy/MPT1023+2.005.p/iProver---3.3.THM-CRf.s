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
% DateTime   : Thu Dec  3 12:07:41 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  197 (2257 expanded)
%              Number of clauses        :  124 ( 801 expanded)
%              Number of leaves         :   22 ( 537 expanded)
%              Depth                    :   29
%              Number of atoms          :  637 (13817 expanded)
%              Number of equality atoms :  320 (3681 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                ( m1_subset_1(X4,X0)
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
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
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
                | ~ m1_subset_1(X4,X0) )
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
              | ~ m1_subset_1(X4,sK2) )
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
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f48,f47])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1094,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1104,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2890,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1094,c_1104])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1097,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1580,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1097])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1594,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1580])).

cnf(c_1735,plain,
    ( sK3 = k1_xboole_0
    | k1_relset_1(sK2,sK3,sK5) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_29,c_1594])).

cnf(c_1736,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1735])).

cnf(c_3023,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2890,c_1736])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1091,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2891,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1091,c_1104])).

cnf(c_1581,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1097])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1809,plain,
    ( sK3 = k1_xboole_0
    | k1_relset_1(sK2,sK3,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1581,c_35])).

cnf(c_1810,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1809])).

cnf(c_3031,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2891,c_1810])).

cnf(c_15,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1107,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3260,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1107])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1405,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1406,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_4105,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3260,c_37,c_39,c_1406])).

cnf(c_4106,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4105])).

cnf(c_4118,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3031,c_4106])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1408,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1409,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_4506,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4118,c_34,c_36,c_1409])).

cnf(c_4513,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_4506])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1105,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2690,plain,
    ( v4_relat_1(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1105])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1109,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3345,plain,
    ( sK3 = k1_xboole_0
    | v4_relat_1(sK5,X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1109])).

cnf(c_3665,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | v4_relat_1(sK5,X0) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3345,c_39,c_1406])).

cnf(c_3666,plain,
    ( sK3 = k1_xboole_0
    | v4_relat_1(sK5,X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3665])).

cnf(c_3674,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_3666])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1113,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1111,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3543,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1111])).

cnf(c_8072,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_3543])).

cnf(c_8496,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4513,c_8072])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_19,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1486,plain,
    ( r2_relset_1(sK2,sK3,X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1657,plain,
    ( r2_relset_1(sK2,sK3,sK5,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_360,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2146,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_2844,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_4077,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_4675,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_361,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2285,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_4304,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_5666,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4304])).

cnf(c_371,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2135,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(sK2,sK3,sK4,sK5)
    | sK5 != X3
    | sK4 != X2
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_2843,plain,
    ( ~ r2_relset_1(X0,sK3,X1,X2)
    | r2_relset_1(sK2,sK3,sK4,sK5)
    | sK5 != X2
    | sK4 != X1
    | sK3 != sK3
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_4218,plain,
    ( ~ r2_relset_1(sK2,sK3,X0,X0)
    | r2_relset_1(sK2,sK3,sK4,sK5)
    | sK5 != X0
    | sK4 != X0
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_6167,plain,
    ( ~ r2_relset_1(sK2,sK3,sK5,sK5)
    | r2_relset_1(sK2,sK3,sK4,sK5)
    | sK5 != sK5
    | sK4 != sK5
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4218])).

cnf(c_8546,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8496,c_28,c_26,c_1657,c_2146,c_2844,c_4077,c_4675,c_5666,c_6167])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1095,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8552,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8546,c_1095])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1108,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9143,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8552,c_1108])).

cnf(c_9144,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9143])).

cnf(c_9308,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9143,c_33,c_31,c_30,c_28,c_26,c_1405,c_1408,c_1657,c_2146,c_2844,c_4077,c_4675,c_5666,c_6167,c_9144])).

cnf(c_9312,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3023,c_9308])).

cnf(c_9313,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9312,c_3031])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1112,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1881,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1112])).

cnf(c_9340,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9313,c_1881])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9365,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9340,c_4])).

cnf(c_1880,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1112])).

cnf(c_9341,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9313,c_1880])).

cnf(c_9362,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9341,c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_213])).

cnf(c_7134,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK0(sK4,X1),X0)
    | ~ r2_hidden(sK0(sK4,X1),sK4) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_7135,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(sK0(sK4,X1),X0) = iProver_top
    | r2_hidden(sK0(sK4,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7134])).

cnf(c_7137,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK4,k1_xboole_0),sK4) != iProver_top
    | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7135])).

cnf(c_7094,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK0(sK5,X1),X0)
    | ~ r2_hidden(sK0(sK5,X1),sK5) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_7095,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r2_hidden(sK0(sK5,X1),X0) = iProver_top
    | r2_hidden(sK0(sK5,X1),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7094])).

cnf(c_7097,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK5,k1_xboole_0),sK5) != iProver_top
    | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7095])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4734,plain,
    ( ~ r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4735,plain,
    ( r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4734])).

cnf(c_4737,plain,
    ( r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4735])).

cnf(c_4268,plain,
    ( ~ r2_hidden(sK0(sK4,X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4269,plain,
    ( r2_hidden(sK0(sK4,X0),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4268])).

cnf(c_4271,plain,
    ( r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_1633,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_4086,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_4091,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4086])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2279,plain,
    ( r2_hidden(sK0(sK4,X0),X0)
    | r2_hidden(sK0(sK4,X0),sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2280,plain,
    ( sK4 = X0
    | r2_hidden(sK0(sK4,X0),X0) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_2282,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK4,k1_xboole_0),sK4) = iProver_top
    | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_2198,plain,
    ( r2_hidden(sK0(sK5,X0),X0)
    | r2_hidden(sK0(sK5,X0),sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2199,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_2201,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK5,k1_xboole_0),sK5) = iProver_top
    | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2199])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9365,c_9362,c_7137,c_7097,c_6167,c_4737,c_4675,c_4271,c_4091,c_2844,c_2282,c_2201,c_2146,c_1657,c_107,c_26,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:10:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.95/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/1.00  
% 3.95/1.00  ------  iProver source info
% 3.95/1.00  
% 3.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/1.00  git: non_committed_changes: false
% 3.95/1.00  git: last_make_outside_of_git: false
% 3.95/1.00  
% 3.95/1.00  ------ 
% 3.95/1.00  ------ Parsing...
% 3.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  ------ Proving...
% 3.95/1.00  ------ Problem Properties 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  clauses                                 34
% 3.95/1.00  conjectures                             8
% 3.95/1.00  EPR                                     8
% 3.95/1.00  Horn                                    27
% 3.95/1.00  unary                                   11
% 3.95/1.00  binary                                  7
% 3.95/1.00  lits                                    84
% 3.95/1.00  lits eq                                 23
% 3.95/1.00  fd_pure                                 0
% 3.95/1.00  fd_pseudo                               0
% 3.95/1.00  fd_cond                                 4
% 3.95/1.00  fd_pseudo_cond                          4
% 3.95/1.00  AC symbols                              0
% 3.95/1.00  
% 3.95/1.00  ------ Input Options Time Limit: Unbounded
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ 
% 3.95/1.00  Current options:
% 3.95/1.00  ------ 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS status Theorem for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  fof(f16,conjecture,(
% 3.95/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f17,negated_conjecture,(
% 3.95/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.95/1.00    inference(negated_conjecture,[],[f16])).
% 3.95/1.00  
% 3.95/1.00  fof(f35,plain,(
% 3.95/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.95/1.00    inference(ennf_transformation,[],[f17])).
% 3.95/1.00  
% 3.95/1.00  fof(f36,plain,(
% 3.95/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.95/1.00    inference(flattening,[],[f35])).
% 3.95/1.00  
% 3.95/1.00  fof(f48,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f47,plain,(
% 3.95/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f49,plain,(
% 3.95/1.00    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f48,f47])).
% 3.95/1.00  
% 3.95/1.00  fof(f81,plain,(
% 3.95/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f13,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f30,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(ennf_transformation,[],[f13])).
% 3.95/1.00  
% 3.95/1.00  fof(f68,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f30])).
% 3.95/1.00  
% 3.95/1.00  fof(f15,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f33,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(ennf_transformation,[],[f15])).
% 3.95/1.00  
% 3.95/1.00  fof(f34,plain,(
% 3.95/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(flattening,[],[f33])).
% 3.95/1.00  
% 3.95/1.00  fof(f46,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(nnf_transformation,[],[f34])).
% 3.95/1.00  
% 3.95/1.00  fof(f70,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f46])).
% 3.95/1.00  
% 3.95/1.00  fof(f80,plain,(
% 3.95/1.00    v1_funct_2(sK5,sK2,sK3)),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f78,plain,(
% 3.95/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f77,plain,(
% 3.95/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f10,axiom,(
% 3.95/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f26,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f10])).
% 3.95/1.00  
% 3.95/1.00  fof(f27,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.95/1.00    inference(flattening,[],[f26])).
% 3.95/1.00  
% 3.95/1.00  fof(f44,plain,(
% 3.95/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f45,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f44])).
% 3.95/1.00  
% 3.95/1.00  fof(f64,plain,(
% 3.95/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f45])).
% 3.95/1.00  
% 3.95/1.00  fof(f79,plain,(
% 3.95/1.00    v1_funct_1(sK5)),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f11,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f28,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(ennf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f66,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f28])).
% 3.95/1.00  
% 3.95/1.00  fof(f76,plain,(
% 3.95/1.00    v1_funct_1(sK4)),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f12,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f19,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.95/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.95/1.00  
% 3.95/1.00  fof(f29,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(ennf_transformation,[],[f19])).
% 3.95/1.00  
% 3.95/1.00  fof(f67,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  fof(f9,axiom,(
% 3.95/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f25,plain,(
% 3.95/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.95/1.00    inference(ennf_transformation,[],[f9])).
% 3.95/1.00  
% 3.95/1.00  fof(f43,plain,(
% 3.95/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.95/1.00    inference(nnf_transformation,[],[f25])).
% 3.95/1.00  
% 3.95/1.00  fof(f62,plain,(
% 3.95/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f43])).
% 3.95/1.00  
% 3.95/1.00  fof(f7,axiom,(
% 3.95/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f42,plain,(
% 3.95/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.95/1.00    inference(nnf_transformation,[],[f7])).
% 3.95/1.00  
% 3.95/1.00  fof(f60,plain,(
% 3.95/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f42])).
% 3.95/1.00  
% 3.95/1.00  fof(f8,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f23,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.95/1.00    inference(ennf_transformation,[],[f8])).
% 3.95/1.00  
% 3.95/1.00  fof(f24,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.95/1.00    inference(flattening,[],[f23])).
% 3.95/1.00  
% 3.95/1.00  fof(f61,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f24])).
% 3.95/1.00  
% 3.95/1.00  fof(f83,plain,(
% 3.95/1.00    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f14,axiom,(
% 3.95/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f31,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.95/1.00    inference(ennf_transformation,[],[f14])).
% 3.95/1.00  
% 3.95/1.00  fof(f32,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.00    inference(flattening,[],[f31])).
% 3.95/1.00  
% 3.95/1.00  fof(f69,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f32])).
% 3.95/1.00  
% 3.95/1.00  fof(f82,plain,(
% 3.95/1.00    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f49])).
% 3.95/1.00  
% 3.95/1.00  fof(f65,plain,(
% 3.95/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f45])).
% 3.95/1.00  
% 3.95/1.00  fof(f59,plain,(
% 3.95/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f42])).
% 3.95/1.00  
% 3.95/1.00  fof(f4,axiom,(
% 3.95/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f40,plain,(
% 3.95/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.95/1.00    inference(nnf_transformation,[],[f4])).
% 3.95/1.00  
% 3.95/1.00  fof(f41,plain,(
% 3.95/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.95/1.00    inference(flattening,[],[f40])).
% 3.95/1.00  
% 3.95/1.00  fof(f56,plain,(
% 3.95/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.95/1.00    inference(cnf_transformation,[],[f41])).
% 3.95/1.00  
% 3.95/1.00  fof(f84,plain,(
% 3.95/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.95/1.00    inference(equality_resolution,[],[f56])).
% 3.95/1.00  
% 3.95/1.00  fof(f5,axiom,(
% 3.95/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f22,plain,(
% 3.95/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f5])).
% 3.95/1.00  
% 3.95/1.00  fof(f57,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f1,axiom,(
% 3.95/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f18,plain,(
% 3.95/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.95/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.95/1.00  
% 3.95/1.00  fof(f20,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.95/1.00    inference(ennf_transformation,[],[f18])).
% 3.95/1.00  
% 3.95/1.00  fof(f50,plain,(
% 3.95/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f20])).
% 3.95/1.00  
% 3.95/1.00  fof(f3,axiom,(
% 3.95/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f21,plain,(
% 3.95/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.95/1.00    inference(ennf_transformation,[],[f3])).
% 3.95/1.00  
% 3.95/1.00  fof(f37,plain,(
% 3.95/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.95/1.00    inference(nnf_transformation,[],[f21])).
% 3.95/1.00  
% 3.95/1.00  fof(f38,plain,(
% 3.95/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f39,plain,(
% 3.95/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.95/1.00  
% 3.95/1.00  fof(f52,plain,(
% 3.95/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f39])).
% 3.95/1.00  
% 3.95/1.00  fof(f2,axiom,(
% 3.95/1.00    v1_xboole_0(k1_xboole_0)),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f51,plain,(
% 3.95/1.00    v1_xboole_0(k1_xboole_0)),
% 3.95/1.00    inference(cnf_transformation,[],[f2])).
% 3.95/1.00  
% 3.95/1.00  cnf(c_28,negated_conjecture,
% 3.95/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1094,plain,
% 3.95/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_18,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1104,plain,
% 3.95/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.95/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2890,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1094,c_1104]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_25,plain,
% 3.95/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.95/1.00      | k1_xboole_0 = X2 ),
% 3.95/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1097,plain,
% 3.95/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.95/1.00      | k1_xboole_0 = X1
% 3.95/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.95/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1580,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | v1_funct_2(sK5,sK2,sK3) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1094,c_1097]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_29,negated_conjecture,
% 3.95/1.00      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.95/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1594,plain,
% 3.95/1.00      ( ~ v1_funct_2(sK5,sK2,sK3)
% 3.95/1.00      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.95/1.00      | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1580]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1735,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0 | k1_relset_1(sK2,sK3,sK5) = sK2 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_1580,c_29,c_1594]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1736,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(renaming,[status(thm)],[c_1735]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3023,plain,
% 3.95/1.00      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_2890,c_1736]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_31,negated_conjecture,
% 3.95/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1091,plain,
% 3.95/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2891,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1091,c_1104]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1581,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1091,c_1097]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_32,negated_conjecture,
% 3.95/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.95/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_35,plain,
% 3.95/1.00      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1809,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0 | k1_relset_1(sK2,sK3,sK4) = sK2 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_1581,c_35]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1810,plain,
% 3.95/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(renaming,[status(thm)],[c_1809]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3031,plain,
% 3.95/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_2891,c_1810]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_15,plain,
% 3.95/1.00      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.95/1.00      | ~ v1_funct_1(X1)
% 3.95/1.00      | ~ v1_funct_1(X0)
% 3.95/1.00      | ~ v1_relat_1(X1)
% 3.95/1.00      | ~ v1_relat_1(X0)
% 3.95/1.00      | X0 = X1
% 3.95/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1107,plain,
% 3.95/1.00      ( X0 = X1
% 3.95/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.95/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.95/1.00      | v1_funct_1(X1) != iProver_top
% 3.95/1.00      | v1_funct_1(X0) != iProver_top
% 3.95/1.00      | v1_relat_1(X0) != iProver_top
% 3.95/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3260,plain,
% 3.95/1.00      ( k1_relat_1(X0) != sK2
% 3.95/1.00      | sK5 = X0
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.95/1.00      | v1_funct_1(X0) != iProver_top
% 3.95/1.00      | v1_funct_1(sK5) != iProver_top
% 3.95/1.00      | v1_relat_1(X0) != iProver_top
% 3.95/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3023,c_1107]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_30,negated_conjecture,
% 3.95/1.00      ( v1_funct_1(sK5) ),
% 3.95/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_37,plain,
% 3.95/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_39,plain,
% 3.95/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_16,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.00      | v1_relat_1(X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1405,plain,
% 3.95/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.95/1.00      | v1_relat_1(sK5) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1406,plain,
% 3.95/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.95/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4105,plain,
% 3.95/1.00      ( v1_relat_1(X0) != iProver_top
% 3.95/1.00      | k1_relat_1(X0) != sK2
% 3.95/1.00      | sK5 = X0
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.95/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_3260,c_37,c_39,c_1406]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4106,plain,
% 3.95/1.00      ( k1_relat_1(X0) != sK2
% 3.95/1.00      | sK5 = X0
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.95/1.00      | v1_funct_1(X0) != iProver_top
% 3.95/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.95/1.00      inference(renaming,[status(thm)],[c_4105]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4118,plain,
% 3.95/1.00      ( sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 3.95/1.00      | v1_funct_1(sK4) != iProver_top
% 3.95/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3031,c_4106]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_33,negated_conjecture,
% 3.95/1.00      ( v1_funct_1(sK4) ),
% 3.95/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_34,plain,
% 3.95/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_36,plain,
% 3.95/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1408,plain,
% 3.95/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.95/1.00      | v1_relat_1(sK4) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1409,plain,
% 3.95/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.95/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4506,plain,
% 3.95/1.00      ( sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_4118,c_34,c_36,c_1409]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4513,plain,
% 3.95/1.00      ( sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK1(sK5,sK4),sK2) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3023,c_4506]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_17,plain,
% 3.95/1.00      ( v4_relat_1(X0,X1)
% 3.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1105,plain,
% 3.95/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.95/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2690,plain,
% 3.95/1.00      ( v4_relat_1(sK5,sK2) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1094,c_1105]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_13,plain,
% 3.95/1.00      ( ~ v4_relat_1(X0,X1)
% 3.95/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.95/1.00      | ~ v1_relat_1(X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1109,plain,
% 3.95/1.00      ( v4_relat_1(X0,X1) != iProver_top
% 3.95/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.95/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3345,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0
% 3.95/1.00      | v4_relat_1(sK5,X0) != iProver_top
% 3.95/1.00      | r1_tarski(sK2,X0) = iProver_top
% 3.95/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3023,c_1109]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3665,plain,
% 3.95/1.00      ( r1_tarski(sK2,X0) = iProver_top
% 3.95/1.00      | v4_relat_1(sK5,X0) != iProver_top
% 3.95/1.00      | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_3345,c_39,c_1406]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3666,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0
% 3.95/1.00      | v4_relat_1(sK5,X0) != iProver_top
% 3.95/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.95/1.00      inference(renaming,[status(thm)],[c_3665]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3674,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_2690,c_3666]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1113,plain,
% 3.95/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.95/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_11,plain,
% 3.95/1.00      ( m1_subset_1(X0,X1)
% 3.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.95/1.00      | ~ r2_hidden(X0,X2) ),
% 3.95/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1111,plain,
% 3.95/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.95/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.95/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3543,plain,
% 3.95/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.95/1.00      | m1_subset_1(X2,X1) = iProver_top
% 3.95/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1113,c_1111]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8072,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0
% 3.95/1.00      | m1_subset_1(X0,sK2) = iProver_top
% 3.95/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3674,c_3543]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8496,plain,
% 3.95/1.00      ( sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_4513,c_8072]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_26,negated_conjecture,
% 3.95/1.00      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 3.95/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_19,plain,
% 3.95/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1486,plain,
% 3.95/1.00      ( r2_relset_1(sK2,sK3,X0,X0)
% 3.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.95/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1657,plain,
% 3.95/1.00      ( r2_relset_1(sK2,sK3,sK5,sK5)
% 3.95/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1486]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_360,plain,( X0 = X0 ),theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2146,plain,
% 3.95/1.00      ( sK2 = sK2 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2844,plain,
% 3.95/1.00      ( sK3 = sK3 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4077,plain,
% 3.95/1.00      ( sK4 = sK4 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4675,plain,
% 3.95/1.00      ( sK5 = sK5 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_361,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2285,plain,
% 3.95/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4304,plain,
% 3.95/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2285]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5666,plain,
% 3.95/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4304]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_371,plain,
% 3.95/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.95/1.00      | r2_relset_1(X4,X5,X6,X7)
% 3.95/1.00      | X4 != X0
% 3.95/1.00      | X5 != X1
% 3.95/1.00      | X6 != X2
% 3.95/1.00      | X7 != X3 ),
% 3.95/1.00      theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2135,plain,
% 3.95/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.95/1.00      | r2_relset_1(sK2,sK3,sK4,sK5)
% 3.95/1.00      | sK5 != X3
% 3.95/1.00      | sK4 != X2
% 3.95/1.00      | sK3 != X1
% 3.95/1.00      | sK2 != X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_371]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2843,plain,
% 3.95/1.00      ( ~ r2_relset_1(X0,sK3,X1,X2)
% 3.95/1.00      | r2_relset_1(sK2,sK3,sK4,sK5)
% 3.95/1.00      | sK5 != X2
% 3.95/1.00      | sK4 != X1
% 3.95/1.00      | sK3 != sK3
% 3.95/1.00      | sK2 != X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2135]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4218,plain,
% 3.95/1.00      ( ~ r2_relset_1(sK2,sK3,X0,X0)
% 3.95/1.00      | r2_relset_1(sK2,sK3,sK4,sK5)
% 3.95/1.00      | sK5 != X0
% 3.95/1.00      | sK4 != X0
% 3.95/1.00      | sK3 != sK3
% 3.95/1.00      | sK2 != sK2 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2843]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6167,plain,
% 3.95/1.00      ( ~ r2_relset_1(sK2,sK3,sK5,sK5)
% 3.95/1.00      | r2_relset_1(sK2,sK3,sK4,sK5)
% 3.95/1.00      | sK5 != sK5
% 3.95/1.00      | sK4 != sK5
% 3.95/1.00      | sK3 != sK3
% 3.95/1.00      | sK2 != sK2 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4218]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8546,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0 | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_8496,c_28,c_26,c_1657,c_2146,c_2844,c_4077,c_4675,
% 3.95/1.00                 c_5666,c_6167]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_27,negated_conjecture,
% 3.95/1.00      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1095,plain,
% 3.95/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 3.95/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8552,plain,
% 3.95/1.00      ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
% 3.95/1.00      | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_8546,c_1095]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_14,plain,
% 3.95/1.00      ( ~ v1_funct_1(X0)
% 3.95/1.00      | ~ v1_funct_1(X1)
% 3.95/1.00      | ~ v1_relat_1(X0)
% 3.95/1.00      | ~ v1_relat_1(X1)
% 3.95/1.00      | X1 = X0
% 3.95/1.00      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.95/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1108,plain,
% 3.95/1.00      ( X0 = X1
% 3.95/1.00      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 3.95/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.95/1.00      | v1_funct_1(X0) != iProver_top
% 3.95/1.00      | v1_funct_1(X1) != iProver_top
% 3.95/1.00      | v1_relat_1(X1) != iProver_top
% 3.95/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9143,plain,
% 3.95/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.95/1.00      | sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0
% 3.95/1.00      | v1_funct_1(sK5) != iProver_top
% 3.95/1.00      | v1_funct_1(sK4) != iProver_top
% 3.95/1.00      | v1_relat_1(sK5) != iProver_top
% 3.95/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_8552,c_1108]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9144,plain,
% 3.95/1.00      ( ~ v1_funct_1(sK5)
% 3.95/1.00      | ~ v1_funct_1(sK4)
% 3.95/1.00      | ~ v1_relat_1(sK5)
% 3.95/1.00      | ~ v1_relat_1(sK4)
% 3.95/1.00      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.95/1.00      | sK5 = sK4
% 3.95/1.00      | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9143]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9308,plain,
% 3.95/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_9143,c_33,c_31,c_30,c_28,c_26,c_1405,c_1408,c_1657,
% 3.95/1.00                 c_2146,c_2844,c_4077,c_4675,c_5666,c_6167,c_9144]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9312,plain,
% 3.95/1.00      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_3023,c_9308]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9313,plain,
% 3.95/1.00      ( sK3 = k1_xboole_0 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_9312,c_3031]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_10,plain,
% 3.95/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1112,plain,
% 3.95/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.95/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1881,plain,
% 3.95/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1091,c_1112]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9340,plain,
% 3.95/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.95/1.00      inference(demodulation,[status(thm)],[c_9313,c_1881]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4,plain,
% 3.95/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.95/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9365,plain,
% 3.95/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(demodulation,[status(thm)],[c_9340,c_4]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1880,plain,
% 3.95/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1094,c_1112]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9341,plain,
% 3.95/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.95/1.00      inference(demodulation,[status(thm)],[c_9313,c_1880]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9362,plain,
% 3.95/1.00      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(demodulation,[status(thm)],[c_9341,c_4]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | ~ r2_hidden(X2,X0)
% 3.95/1.00      | r2_hidden(X2,X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_213,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.95/1.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_280,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.95/1.00      inference(bin_hyper_res,[status(thm)],[c_7,c_213]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7134,plain,
% 3.95/1.00      ( ~ r1_tarski(sK4,X0)
% 3.95/1.00      | r2_hidden(sK0(sK4,X1),X0)
% 3.95/1.00      | ~ r2_hidden(sK0(sK4,X1),sK4) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_280]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7135,plain,
% 3.95/1.00      ( r1_tarski(sK4,X0) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,X1),X0) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,X1),sK4) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7134]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7137,plain,
% 3.95/1.00      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,k1_xboole_0),sK4) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_7135]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7094,plain,
% 3.95/1.00      ( ~ r1_tarski(sK5,X0)
% 3.95/1.00      | r2_hidden(sK0(sK5,X1),X0)
% 3.95/1.00      | ~ r2_hidden(sK0(sK5,X1),sK5) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_280]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7095,plain,
% 3.95/1.00      ( r1_tarski(sK5,X0) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,X1),X0) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,X1),sK5) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7094]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7097,plain,
% 3.95/1.00      ( r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,k1_xboole_0),sK5) != iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_7095]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_0,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4734,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(sK5,X0),X0) | ~ v1_xboole_0(X0) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4735,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK5,X0),X0) != iProver_top
% 3.95/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_4734]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4737,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.95/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4735]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4268,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(sK4,X0),X0) | ~ v1_xboole_0(X0) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4269,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK4,X0),X0) != iProver_top
% 3.95/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_4268]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4271,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.95/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4269]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1633,plain,
% 3.95/1.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4086,plain,
% 3.95/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4091,plain,
% 3.95/1.00      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4086]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3,plain,
% 3.95/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X0 = X1 ),
% 3.95/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2279,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK4,X0),X0)
% 3.95/1.00      | r2_hidden(sK0(sK4,X0),sK4)
% 3.95/1.00      | sK4 = X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2280,plain,
% 3.95/1.00      ( sK4 = X0
% 3.95/1.00      | r2_hidden(sK0(sK4,X0),X0) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,X0),sK4) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2279]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2282,plain,
% 3.95/1.00      ( sK4 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK0(sK4,k1_xboole_0),sK4) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2280]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2198,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK5,X0),X0)
% 3.95/1.00      | r2_hidden(sK0(sK5,X0),sK5)
% 3.95/1.00      | sK5 = X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2199,plain,
% 3.95/1.00      ( sK5 = X0
% 3.95/1.00      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,X0),sK5) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2198]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2201,plain,
% 3.95/1.00      ( sK5 = k1_xboole_0
% 3.95/1.00      | r2_hidden(sK0(sK5,k1_xboole_0),sK5) = iProver_top
% 3.95/1.00      | r2_hidden(sK0(sK5,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2199]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1,plain,
% 3.95/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_107,plain,
% 3.95/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(contradiction,plain,
% 3.95/1.00      ( $false ),
% 3.95/1.00      inference(minisat,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_9365,c_9362,c_7137,c_7097,c_6167,c_4737,c_4675,c_4271,
% 3.95/1.00                 c_4091,c_2844,c_2282,c_2201,c_2146,c_1657,c_107,c_26,
% 3.95/1.00                 c_28]) ).
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  ------                               Statistics
% 3.95/1.00  
% 3.95/1.00  ------ Selected
% 3.95/1.00  
% 3.95/1.00  total_time:                             0.279
% 3.95/1.00  
%------------------------------------------------------------------------------
