%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:36 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  158 (1765 expanded)
%              Number of clauses        :  109 ( 616 expanded)
%              Number of leaves         :   13 ( 416 expanded)
%              Depth                    :   25
%              Number of atoms          :  543 (12263 expanded)
%              Number of equality atoms :  277 (3331 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
             => ( v2_funct_1(X3)
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( ~ v2_funct_1(X3)
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X2 )
        & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_1(X3)
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_1(sK3)
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_funct_1(sK3)
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f46,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_356,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_19])).

cnf(c_496,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_504,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_822,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_815,plain,
    ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1215,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_822,c_815])).

cnf(c_1324,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_496,c_1215])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | v2_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X3))
    | k1_relat_1(X3) != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_234,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_502,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48)))
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_funct_1(X1_48)
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k5_relat_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_234])).

cnf(c_824,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48))) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_2026,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK0)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_824])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_963,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_964,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_518,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_982,plain,
    ( sK1 != X0_48
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_1142,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_516,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1143,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_506,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_820,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48) = k5_relat_1(X3_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_817,plain,
    ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X4_48,X5_48) = k5_relat_1(X4_48,X5_48)
    | m1_subset_1(X5_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X5_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_1420,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_817])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1720,plain,
    ( v1_funct_1(X2_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_25])).

cnf(c_1721,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_1720])).

cnf(c_1730,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_1721])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1_48,X2_48,X3_48,X4_48,X0_48,sK4) = k5_relat_1(X0_48,sK4) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2_48,X3_48,X0_48,X1_48,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_48,X1_48,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1237,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_1802,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_21,c_19,c_18,c_16,c_1237])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_507,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_819,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_1805,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1802,c_819])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_281,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_501,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_825,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_534,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_508,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1276,plain,
    ( sK2 != X0_48
    | k1_xboole_0 != X0_48
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_1277,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_2048,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_534,c_508,c_1277])).

cnf(c_2049,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_2048])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_816,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1224,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_822,c_816])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_814,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1372,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1224,c_814])).

cnf(c_1483,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_24])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_343,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_345,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_16])).

cnf(c_497,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_1214,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_820,c_815])).

cnf(c_1284,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_497,c_1214])).

cnf(c_1944,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_824])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_960,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_961,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_2086,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1944,c_25,c_27,c_961])).

cnf(c_2087,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2086])).

cnf(c_2098,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2087])).

cnf(c_2101,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2026,c_22,c_24,c_29,c_964,c_1142,c_1143,c_1805,c_2049,c_2098])).

cnf(c_2116,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2101,c_1483])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK4 != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_317,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_827,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_2118,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2101,c_827])).

cnf(c_2144,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2118])).

cnf(c_2122,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2101,c_1214])).

cnf(c_2145,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2144,c_2122])).

cnf(c_2126,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2101,c_820])).

cnf(c_2148,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2145,c_2126])).

cnf(c_2286,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2148,c_824])).

cnf(c_4317,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_25,c_27,c_961])).

cnf(c_4318,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4317])).

cnf(c_4328,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2116,c_4318])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4328,c_1805,c_964,c_29,c_24,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 2.88/0.99  clauses                                 19
% 2.88/0.99  conjectures                             7
% 2.88/0.99  EPR                                     4
% 2.88/0.99  Horn                                    15
% 2.88/0.99  unary                                   6
% 2.88/0.99  binary                                  7
% 2.88/0.99  lits                                    46
% 2.88/0.99  lits eq                                 19
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 0
% 2.88/0.99  fd_pseudo_cond                          0
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
% 2.88/0.99  fof(f7,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f19,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f7])).
% 2.88/0.99  
% 2.88/0.99  fof(f20,plain,(
% 2.88/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(flattening,[],[f19])).
% 2.88/0.99  
% 2.88/0.99  fof(f25,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(nnf_transformation,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f35,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f9,conjecture,(
% 2.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f10,negated_conjecture,(
% 2.88/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.88/0.99    inference(negated_conjecture,[],[f9])).
% 2.88/0.99  
% 2.88/0.99  fof(f23,plain,(
% 2.88/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.88/0.99    inference(ennf_transformation,[],[f10])).
% 2.88/0.99  
% 2.88/0.99  fof(f24,plain,(
% 2.88/0.99    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.88/0.99    inference(flattening,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f27,plain,(
% 2.88/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f26,plain,(
% 2.88/0.99    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f28,plain,(
% 2.88/0.99    (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26])).
% 2.88/0.99  
% 2.88/0.99  fof(f43,plain,(
% 2.88/0.99    v1_funct_2(sK3,sK0,sK1)),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f44,plain,(
% 2.88/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f5,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f17,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f5])).
% 2.88/0.99  
% 2.88/0.99  fof(f33,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f17])).
% 2.88/0.99  
% 2.88/0.99  fof(f1,axiom,(
% 2.88/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f11,plain,(
% 2.88/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.88/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.88/0.99  
% 2.88/0.99  fof(f12,plain,(
% 2.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.88/0.99    inference(ennf_transformation,[],[f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f29,plain,(
% 2.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f12])).
% 2.88/0.99  
% 2.88/0.99  fof(f2,axiom,(
% 2.88/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f13,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f2])).
% 2.88/0.99  
% 2.88/0.99  fof(f14,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/0.99    inference(flattening,[],[f13])).
% 2.88/0.99  
% 2.88/0.99  fof(f30,plain,(
% 2.88/0.99    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f14])).
% 2.88/0.99  
% 2.88/0.99  fof(f42,plain,(
% 2.88/0.99    v1_funct_1(sK3)),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f50,plain,(
% 2.88/0.99    ~v2_funct_1(sK3)),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f3,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f15,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f3])).
% 2.88/0.99  
% 2.88/0.99  fof(f31,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f15])).
% 2.88/0.99  
% 2.88/0.99  fof(f47,plain,(
% 2.88/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f8,axiom,(
% 2.88/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f21,plain,(
% 2.88/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.88/0.99    inference(ennf_transformation,[],[f8])).
% 2.88/0.99  
% 2.88/0.99  fof(f22,plain,(
% 2.88/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.88/0.99    inference(flattening,[],[f21])).
% 2.88/0.99  
% 2.88/0.99  fof(f41,plain,(
% 2.88/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f22])).
% 2.88/0.99  
% 2.88/0.99  fof(f45,plain,(
% 2.88/0.99    v1_funct_1(sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f48,plain,(
% 2.88/0.99    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f39,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f53,plain,(
% 2.88/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.88/0.99    inference(equality_resolution,[],[f39])).
% 2.88/0.99  
% 2.88/0.99  fof(f46,plain,(
% 2.88/0.99    v1_funct_2(sK4,sK1,sK2)),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f49,plain,(
% 2.88/0.99    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.88/0.99    inference(cnf_transformation,[],[f28])).
% 2.88/0.99  
% 2.88/0.99  fof(f6,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f18,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f6])).
% 2.88/0.99  
% 2.88/0.99  fof(f34,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f18])).
% 2.88/0.99  
% 2.88/0.99  fof(f4,axiom,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f16,plain,(
% 2.88/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/0.99    inference(ennf_transformation,[],[f4])).
% 2.88/0.99  
% 2.88/0.99  fof(f32,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f36,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f55,plain,(
% 2.88/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.88/0.99    inference(equality_resolution,[],[f36])).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_20,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_353,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | sK0 != X1
% 2.88/0.99      | sK1 != X2
% 2.88/0.99      | sK3 != X0
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_354,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.88/0.99      | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_19,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_356,plain,
% 2.88/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_354,c_19]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_496,plain,
% 2.88/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_356]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_504,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_822,plain,
% 2.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_512,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_815,plain,
% 2.88/0.99      ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
% 2.88/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1215,plain,
% 2.88/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_822,c_815]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1324,plain,
% 2.88/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_496,c_1215]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_0,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1,plain,
% 2.88/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_233,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.88/0.99      | ~ v1_relat_1(X2)
% 2.88/0.99      | ~ v1_relat_1(X3)
% 2.88/0.99      | ~ v1_funct_1(X3)
% 2.88/0.99      | ~ v1_funct_1(X2)
% 2.88/0.99      | v2_funct_1(X2)
% 2.88/0.99      | ~ v2_funct_1(k5_relat_1(X2,X3))
% 2.88/0.99      | k1_relat_1(X3) != X1
% 2.88/0.99      | k2_relat_1(X2) != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_234,plain,
% 2.88/0.99      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.88/0.99      | ~ v1_relat_1(X0)
% 2.88/0.99      | ~ v1_relat_1(X1)
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | v2_funct_1(X0)
% 2.88/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1)) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_502,plain,
% 2.88/0.99      ( ~ m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48)))
% 2.88/0.99      | ~ v1_relat_1(X0_48)
% 2.88/0.99      | ~ v1_relat_1(X1_48)
% 2.88/0.99      | ~ v1_funct_1(X1_48)
% 2.88/0.99      | ~ v1_funct_1(X0_48)
% 2.88/0.99      | v2_funct_1(X0_48)
% 2.88/0.99      | ~ v2_funct_1(k5_relat_1(X0_48,X1_48)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_234]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_824,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48))) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_relat_1(X1_48) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(X1_48) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,X1_48)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2026,plain,
% 2.88/0.99      ( sK1 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK0)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_relat_1(sK3) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(sK3) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK3)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1324,c_824]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_21,negated_conjecture,
% 2.88/0.99      ( v1_funct_1(sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_22,plain,
% 2.88/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_24,plain,
% 2.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_13,negated_conjecture,
% 2.88/0.99      ( ~ v2_funct_1(sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_29,plain,
% 2.88/0.99      ( v2_funct_1(sK3) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | v1_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_514,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | v1_relat_1(X0_48) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_963,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/0.99      | v1_relat_1(sK3) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_514]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_964,plain,
% 2.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.88/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_518,plain,
% 2.88/0.99      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.88/0.99      theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_982,plain,
% 2.88/0.99      ( sK1 != X0_48 | sK1 = k1_xboole_0 | k1_xboole_0 != X0_48 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_518]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1142,plain,
% 2.88/0.99      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_982]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_516,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1143,plain,
% 2.88/0.99      ( sK1 = sK1 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_516]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_16,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_506,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_820,plain,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_12,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.88/0.99      | ~ v1_funct_1(X0)
% 2.88/0.99      | ~ v1_funct_1(X3)
% 2.88/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_510,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.88/0.99      | ~ v1_funct_1(X0_48)
% 2.88/0.99      | ~ v1_funct_1(X3_48)
% 2.88/0.99      | k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48) = k5_relat_1(X3_48,X0_48) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_817,plain,
% 2.88/0.99      ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X4_48,X5_48) = k5_relat_1(X4_48,X5_48)
% 2.88/0.99      | m1_subset_1(X5_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.88/0.99      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.88/0.99      | v1_funct_1(X5_48) != iProver_top
% 2.88/0.99      | v1_funct_1(X4_48) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1420,plain,
% 2.88/0.99      ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
% 2.88/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.88/0.99      | v1_funct_1(X2_48) != iProver_top
% 2.88/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_820,c_817]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_18,negated_conjecture,
% 2.88/0.99      ( v1_funct_1(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_25,plain,
% 2.88/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1720,plain,
% 2.88/0.99      ( v1_funct_1(X2_48) != iProver_top
% 2.88/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.88/0.99      | k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_1420,c_25]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1721,plain,
% 2.88/0.99      ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
% 2.88/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.88/0.99      | v1_funct_1(X2_48) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_1720]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1730,plain,
% 2.88/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_822,c_1721]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1015,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_48,X4_48)))
% 2.88/0.99      | ~ v1_funct_1(X0_48)
% 2.88/0.99      | ~ v1_funct_1(sK4)
% 2.88/0.99      | k1_partfun1(X1_48,X2_48,X3_48,X4_48,X0_48,sK4) = k5_relat_1(X0_48,sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_510]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1088,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 2.88/0.99      | ~ v1_funct_1(sK4)
% 2.88/0.99      | ~ v1_funct_1(sK3)
% 2.88/0.99      | k1_partfun1(X2_48,X3_48,X0_48,X1_48,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1015]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1107,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.88/0.99      | ~ v1_funct_1(sK4)
% 2.88/0.99      | ~ v1_funct_1(sK3)
% 2.88/0.99      | k1_partfun1(X0_48,X1_48,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1088]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1237,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/0.99      | ~ v1_funct_1(sK4)
% 2.88/0.99      | ~ v1_funct_1(sK3)
% 2.88/0.99      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1107]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1802,plain,
% 2.88/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_1730,c_21,c_19,c_18,c_16,c_1237]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_15,negated_conjecture,
% 2.88/0.99      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_507,negated_conjecture,
% 2.88/0.99      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_819,plain,
% 2.88/0.99      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1805,plain,
% 2.88/0.99      ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_1802,c_819]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.88/0.99      | k1_xboole_0 = X1
% 2.88/0.99      | k1_xboole_0 = X0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_17,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.88/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_280,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | sK2 != k1_xboole_0
% 2.88/0.99      | sK1 != X1
% 2.88/0.99      | k1_xboole_0 = X0
% 2.88/0.99      | k1_xboole_0 = X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_281,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.88/0.99      | sK2 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK4
% 2.88/0.99      | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_501,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.88/0.99      | sK2 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK4
% 2.88/0.99      | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_281]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_825,plain,
% 2.88/0.99      ( sK2 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK4
% 2.88/0.99      | k1_xboole_0 = sK1
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_534,plain,
% 2.88/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_516]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_14,negated_conjecture,
% 2.88/0.99      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_508,negated_conjecture,
% 2.88/0.99      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1276,plain,
% 2.88/0.99      ( sK2 != X0_48 | k1_xboole_0 != X0_48 | k1_xboole_0 = sK2 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_518]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1277,plain,
% 2.88/0.99      ( sK2 != k1_xboole_0
% 2.88/0.99      | k1_xboole_0 = sK2
% 2.88/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_1276]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2048,plain,
% 2.88/0.99      ( k1_xboole_0 = sK1 | sK2 != k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_825,c_534,c_508,c_1277]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2049,plain,
% 2.88/0.99      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_2048]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_511,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_816,plain,
% 2.88/0.99      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.88/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1224,plain,
% 2.88/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_822,c_816]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_513,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.88/0.99      | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_814,plain,
% 2.88/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.88/0.99      | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1372,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1224,c_814]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1483,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_1372,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_342,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | sK2 != X2
% 2.88/0.99      | sK1 != X1
% 2.88/0.99      | k1_xboole_0 = X2 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_343,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.88/0.99      | k1_xboole_0 = sK2 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_345,plain,
% 2.88/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_343,c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_497,plain,
% 2.88/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_345]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1214,plain,
% 2.88/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_820,c_815]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1284,plain,
% 2.88/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_497,c_1214]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1944,plain,
% 2.88/0.99      ( sK2 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(sK4) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1284,c_824]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_27,plain,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_960,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/0.99      | v1_relat_1(sK4) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_514]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_961,plain,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.88/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2086,plain,
% 2.88/0.99      ( v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | sK2 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_1944,c_25,c_27,c_961]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2087,plain,
% 2.88/0.99      ( sK2 = k1_xboole_0
% 2.88/0.99      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_2086]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2098,plain,
% 2.88/0.99      ( sK2 = k1_xboole_0
% 2.88/0.99      | v1_relat_1(sK3) != iProver_top
% 2.88/0.99      | v1_funct_1(sK3) != iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.88/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_1483,c_2087]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2101,plain,
% 2.88/0.99      ( sK1 = k1_xboole_0 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2026,c_22,c_24,c_29,c_964,c_1142,c_1143,c_1805,c_2049,
% 2.88/0.99                 c_2098]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2116,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_2101,c_1483]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_10,plain,
% 2.88/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_316,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | sK2 != X1
% 2.88/0.99      | sK1 != k1_xboole_0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_317,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.88/0.99      | sK1 != k1_xboole_0 ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_499,plain,
% 2.88/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.88/0.99      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.88/0.99      | sK1 != k1_xboole_0 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_317]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_827,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.88/0.99      | sK1 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2118,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.88/0.99      | k1_xboole_0 != k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_2101,c_827]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2144,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_2118]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2122,plain,
% 2.88/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_2101,c_1214]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2145,plain,
% 2.88/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 2.88/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_2144,c_2122]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2126,plain,
% 2.88/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 2.88/0.99      inference(demodulation,[status(thm)],[c_2101,c_820]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2148,plain,
% 2.88/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.88/0.99      inference(forward_subsumption_resolution,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2145,c_2126]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2286,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_relat_1(sK4) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(sK4) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2148,c_824]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4317,plain,
% 2.88/0.99      ( v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2286,c_25,c_27,c_961]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4318,plain,
% 2.88/0.99      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.88/0.99      | v1_relat_1(X0_48) != iProver_top
% 2.88/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.88/0.99      | v2_funct_1(X0_48) = iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_4317]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4328,plain,
% 2.88/0.99      ( v1_relat_1(sK3) != iProver_top
% 2.88/0.99      | v1_funct_1(sK3) != iProver_top
% 2.88/0.99      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.88/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2116,c_4318]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(contradiction,plain,
% 2.88/0.99      ( $false ),
% 2.88/0.99      inference(minisat,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4328,c_1805,c_964,c_29,c_24,c_22]) ).
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
% 2.88/0.99  out_proof_time:                         0.01
% 2.88/0.99  total_time:                             0.167
% 2.88/0.99  num_of_symbols:                         53
% 2.88/0.99  num_of_terms:                           3430
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing
% 2.88/0.99  
% 2.88/0.99  num_of_splits:                          0
% 2.88/0.99  num_of_split_atoms:                     0
% 2.88/0.99  num_of_reused_defs:                     0
% 2.88/0.99  num_eq_ax_congr_red:                    26
% 2.88/0.99  num_of_sem_filtered_clauses:            1
% 2.88/0.99  num_of_subtypes:                        2
% 2.88/0.99  monotx_restored_types:                  0
% 2.88/0.99  sat_num_of_epr_types:                   0
% 2.88/0.99  sat_num_of_non_cyclic_types:            0
% 2.88/0.99  sat_guarded_non_collapsed_types:        0
% 2.88/0.99  num_pure_diseq_elim:                    0
% 2.88/0.99  simp_replaced_by:                       0
% 2.88/0.99  res_preprocessed:                       100
% 2.88/0.99  prep_upred:                             0
% 2.88/0.99  prep_unflattend:                        36
% 2.88/0.99  smt_new_axioms:                         0
% 2.88/0.99  pred_elim_cands:                        4
% 2.88/0.99  pred_elim:                              2
% 2.88/0.99  pred_elim_cl:                           3
% 2.88/0.99  pred_elim_cycles:                       4
% 2.88/0.99  merged_defs:                            0
% 2.88/0.99  merged_defs_ncl:                        0
% 2.88/0.99  bin_hyper_res:                          0
% 2.88/0.99  prep_cycles:                            4
% 2.88/0.99  pred_elim_time:                         0.004
% 2.88/0.99  splitting_time:                         0.
% 2.88/0.99  sem_filter_time:                        0.
% 2.88/0.99  monotx_time:                            0.
% 2.88/0.99  subtype_inf_time:                       0.
% 2.88/0.99  
% 2.88/0.99  ------ Problem properties
% 2.88/0.99  
% 2.88/0.99  clauses:                                19
% 2.88/0.99  conjectures:                            7
% 2.88/0.99  epr:                                    4
% 2.88/0.99  horn:                                   15
% 2.88/0.99  ground:                                 13
% 2.88/0.99  unary:                                  6
% 2.88/0.99  binary:                                 7
% 2.88/0.99  lits:                                   46
% 2.88/0.99  lits_eq:                                19
% 2.88/0.99  fd_pure:                                0
% 2.88/0.99  fd_pseudo:                              0
% 2.88/0.99  fd_cond:                                0
% 2.88/0.99  fd_pseudo_cond:                         0
% 2.88/1.00  ac_symbols:                             0
% 2.88/1.00  
% 2.88/1.00  ------ Propositional Solver
% 2.88/1.00  
% 2.88/1.00  prop_solver_calls:                      29
% 2.88/1.00  prop_fast_solver_calls:                 791
% 2.88/1.00  smt_solver_calls:                       0
% 2.88/1.00  smt_fast_solver_calls:                  0
% 2.88/1.00  prop_num_of_clauses:                    1438
% 2.88/1.00  prop_preprocess_simplified:             3602
% 2.88/1.00  prop_fo_subsumed:                       29
% 2.88/1.00  prop_solver_time:                       0.
% 2.88/1.00  smt_solver_time:                        0.
% 2.88/1.00  smt_fast_solver_time:                   0.
% 2.88/1.00  prop_fast_solver_time:                  0.
% 2.88/1.00  prop_unsat_core_time:                   0.
% 2.88/1.00  
% 2.88/1.00  ------ QBF
% 2.88/1.00  
% 2.88/1.00  qbf_q_res:                              0
% 2.88/1.00  qbf_num_tautologies:                    0
% 2.88/1.00  qbf_prep_cycles:                        0
% 2.88/1.00  
% 2.88/1.00  ------ BMC1
% 2.88/1.00  
% 2.88/1.00  bmc1_current_bound:                     -1
% 2.88/1.00  bmc1_last_solved_bound:                 -1
% 2.88/1.00  bmc1_unsat_core_size:                   -1
% 2.88/1.00  bmc1_unsat_core_parents_size:           -1
% 2.88/1.00  bmc1_merge_next_fun:                    0
% 2.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation
% 2.88/1.00  
% 2.88/1.00  inst_num_of_clauses:                    588
% 2.88/1.00  inst_num_in_passive:                    152
% 2.88/1.00  inst_num_in_active:                     353
% 2.88/1.00  inst_num_in_unprocessed:                83
% 2.88/1.00  inst_num_of_loops:                      460
% 2.88/1.00  inst_num_of_learning_restarts:          0
% 2.88/1.00  inst_num_moves_active_passive:          103
% 2.88/1.00  inst_lit_activity:                      0
% 2.88/1.00  inst_lit_activity_moves:                0
% 2.88/1.00  inst_num_tautologies:                   0
% 2.88/1.00  inst_num_prop_implied:                  0
% 2.88/1.00  inst_num_existing_simplified:           0
% 2.88/1.00  inst_num_eq_res_simplified:             0
% 2.88/1.00  inst_num_child_elim:                    0
% 2.88/1.00  inst_num_of_dismatching_blockings:      73
% 2.88/1.00  inst_num_of_non_proper_insts:           553
% 2.88/1.00  inst_num_of_duplicates:                 0
% 2.88/1.00  inst_inst_num_from_inst_to_res:         0
% 2.88/1.00  inst_dismatching_checking_time:         0.
% 2.88/1.00  
% 2.88/1.00  ------ Resolution
% 2.88/1.00  
% 2.88/1.00  res_num_of_clauses:                     0
% 2.88/1.00  res_num_in_passive:                     0
% 2.88/1.00  res_num_in_active:                      0
% 2.88/1.00  res_num_of_loops:                       104
% 2.88/1.00  res_forward_subset_subsumed:            84
% 2.88/1.00  res_backward_subset_subsumed:           2
% 2.88/1.00  res_forward_subsumed:                   0
% 2.88/1.00  res_backward_subsumed:                  0
% 2.88/1.00  res_forward_subsumption_resolution:     0
% 2.88/1.00  res_backward_subsumption_resolution:    0
% 2.88/1.00  res_clause_to_clause_subsumption:       273
% 2.88/1.00  res_orphan_elimination:                 0
% 2.88/1.00  res_tautology_del:                      147
% 2.88/1.00  res_num_eq_res_simplified:              0
% 2.88/1.00  res_num_sel_changes:                    0
% 2.88/1.00  res_moves_from_active_to_pass:          0
% 2.88/1.00  
% 2.88/1.00  ------ Superposition
% 2.88/1.00  
% 2.88/1.00  sup_time_total:                         0.
% 2.88/1.00  sup_time_generating:                    0.
% 2.88/1.00  sup_time_sim_full:                      0.
% 2.88/1.00  sup_time_sim_immed:                     0.
% 2.88/1.00  
% 2.88/1.00  sup_num_of_clauses:                     71
% 2.88/1.00  sup_num_in_active:                      56
% 2.88/1.00  sup_num_in_passive:                     15
% 2.88/1.00  sup_num_of_loops:                       90
% 2.88/1.00  sup_fw_superposition:                   57
% 2.88/1.00  sup_bw_superposition:                   40
% 2.88/1.00  sup_immediate_simplified:               24
% 2.88/1.00  sup_given_eliminated:                   0
% 2.88/1.00  comparisons_done:                       0
% 2.88/1.00  comparisons_avoided:                    20
% 2.88/1.00  
% 2.88/1.00  ------ Simplifications
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  sim_fw_subset_subsumed:                 18
% 2.88/1.00  sim_bw_subset_subsumed:                 3
% 2.88/1.00  sim_fw_subsumed:                        0
% 2.88/1.00  sim_bw_subsumed:                        0
% 2.88/1.00  sim_fw_subsumption_res:                 3
% 2.88/1.00  sim_bw_subsumption_res:                 0
% 2.88/1.00  sim_tautology_del:                      0
% 2.88/1.00  sim_eq_tautology_del:                   3
% 2.88/1.00  sim_eq_res_simp:                        2
% 2.88/1.00  sim_fw_demodulated:                     1
% 2.88/1.00  sim_bw_demodulated:                     36
% 2.88/1.00  sim_light_normalised:                   3
% 2.88/1.00  sim_joinable_taut:                      0
% 2.88/1.00  sim_joinable_simp:                      0
% 2.88/1.00  sim_ac_normalised:                      0
% 2.88/1.00  sim_smt_subsumption:                    0
% 2.88/1.00  
%------------------------------------------------------------------------------
