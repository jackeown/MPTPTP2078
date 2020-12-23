%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0974+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:32 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 403 expanded)
%              Number of clauses        :   78 ( 136 expanded)
%              Number of leaves         :   12 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  407 (2787 expanded)
%              Number of equality atoms :  201 (1228 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2
        & k1_xboole_0 != X2
        & k2_relset_1(X1,X2,sK4) = X2
        & k2_relset_1(X0,X1,X3) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2
          & k1_xboole_0 != sK2
          & k2_relset_1(sK1,sK2,X4) = sK2
          & k2_relset_1(sK0,sK1,sK3) = sK1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2
    & k1_xboole_0 != sK2
    & k2_relset_1(sK1,sK2,sK4) = sK2
    & k2_relset_1(sK0,sK1,sK3) = sK1
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f30,f29])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_497,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_809,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_499,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_807,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_801,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X3_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_806,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1692,plain,
    ( k2_relset_1(X0_47,X1_47,k1_partfun1(X0_47,X2_47,X3_47,X1_47,X4_47,X5_47)) = k2_relat_1(k1_partfun1(X0_47,X2_47,X3_47,X1_47,X4_47,X5_47))
    | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X3_47,X1_47))) != iProver_top
    | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X2_47))) != iProver_top
    | v1_funct_1(X5_47) != iProver_top
    | v1_funct_1(X4_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_806])).

cnf(c_3633,plain,
    ( k2_relset_1(X0_47,sK2,k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4)) = k2_relat_1(k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4))
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_1692])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3734,plain,
    ( v1_funct_1(X2_47) != iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k2_relset_1(X0_47,sK2,k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4)) = k2_relat_1(k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_28])).

cnf(c_3735,plain,
    ( k2_relset_1(X0_47,sK2,k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4)) = k2_relat_1(k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4))
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_3734])).

cnf(c_3744,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_3735])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_804,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
    | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X5_47) != iProver_top
    | v1_funct_1(X4_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1907,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_804])).

cnf(c_1979,plain,
    ( v1_funct_1(X2_47) != iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1907,c_28])).

cnf(c_1980,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1979])).

cnf(c_1989,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_1980])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2091,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1989,c_25])).

cnf(c_1291,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_809,c_806])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_500,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1293,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1291,c_500])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_805,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_1215,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_807,c_805])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK1 != X1
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_339,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_341,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_19,c_16])).

cnf(c_490,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_1220,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1215,c_490])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) != X1
    | k2_relat_1(k5_relat_1(X3,X2)) = k2_relat_1(X2)
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_242,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k2_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_495,plain,
    ( ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k2_relat_1(X1_47)))
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | k2_relat_1(k5_relat_1(X1_47,X0_47)) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_811,plain,
    ( k2_relat_1(k5_relat_1(X0_47,X1_47)) = k2_relat_1(X1_47)
    | m1_subset_1(k1_relat_1(X1_47),k1_zfmisc_1(k2_relat_1(X0_47))) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2812,plain,
    ( k2_relat_1(k5_relat_1(X0_47,sK4)) = k2_relat_1(sK4)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(X0_47))) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_811])).

cnf(c_1290,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_807,c_806])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_501,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1296,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1290,c_501])).

cnf(c_2847,plain,
    ( k2_relat_1(k5_relat_1(X0_47,sK4)) = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(X0_47))) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2812,c_1296])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_956,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_957,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_2937,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(X0_47))) != iProver_top
    | k2_relat_1(k5_relat_1(X0_47,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2847,c_30,c_957])).

cnf(c_2938,plain,
    ( k2_relat_1(k5_relat_1(X0_47,sK4)) = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(X0_47))) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2937])).

cnf(c_2947,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_2938])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_959,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_960,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_803,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_1796,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_490,c_803])).

cnf(c_2990,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_27,c_30,c_960,c_1796])).

cnf(c_3778,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3744,c_2091,c_2990])).

cnf(c_15,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_503,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2094,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_2091,c_503])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3778,c_2094,c_25])).


%------------------------------------------------------------------------------
