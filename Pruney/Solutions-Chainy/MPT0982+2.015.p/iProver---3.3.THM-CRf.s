%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:40 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  159 (1100 expanded)
%              Number of clauses        :   94 ( 345 expanded)
%              Number of leaves         :   16 ( 265 expanded)
%              Depth                    :   22
%              Number of atoms          :  479 (7445 expanded)
%              Number of equality atoms :  212 (2491 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1009,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1011,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1012,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2478,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1012])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2641,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2478,c_35])).

cnf(c_2642,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2641])).

cnf(c_2649,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_2642])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2722,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_32])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2725,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_1014])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4539,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2725,c_32,c_34,c_35,c_37])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1015,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4546,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4539,c_1015])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2724,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2722,c_25])).

cnf(c_4550,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4546,c_2724])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1018,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4560,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4550,c_1018])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1133,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_5354,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4560,c_34,c_37,c_1133,c_1320])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_9])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_2394,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1006])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1022,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2593,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1022])).

cnf(c_5359,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_5354,c_2593])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1021,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_28])).

cnf(c_1007,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_330,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1682,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_37,c_330,c_1133])).

cnf(c_1683,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1682])).

cnf(c_1688,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1021,c_1683])).

cnf(c_1017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1352,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1017])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1020,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1408,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1352,c_1020])).

cnf(c_1689,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_1688,c_1408])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1016,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1774,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1011,c_1016])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_445,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_447,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_26,c_23])).

cnf(c_1776,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1774,c_447])).

cnf(c_3014,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1689,c_1689,c_1776])).

cnf(c_22297,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_5359,c_3014])).

cnf(c_2395,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1006])).

cnf(c_1963,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1776,c_1683])).

cnf(c_2597,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2395,c_1963])).

cnf(c_1353,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1017])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1019,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1829,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1019])).

cnf(c_2276,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1353,c_1829])).

cnf(c_2598,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2597,c_2276])).

cnf(c_8093,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2598,c_2598,c_4550])).

cnf(c_22462,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_22297,c_8093])).

cnf(c_1406,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1009,c_1015])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1544,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1406,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22462,c_1544])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     num_symb
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       true
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 26
% 7.75/1.50  conjectures                             7
% 7.75/1.50  EPR                                     5
% 7.75/1.50  Horn                                    23
% 7.75/1.50  unary                                   9
% 7.75/1.50  binary                                  6
% 7.75/1.50  lits                                    62
% 7.75/1.50  lits eq                                 23
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 0
% 7.75/1.50  fd_pseudo_cond                          1
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Schedule dynamic 5 is on 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     none
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       false
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f14,conjecture,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f15,negated_conjecture,(
% 7.75/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.75/1.50    inference(negated_conjecture,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.75/1.50    inference(ennf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f69,plain,(
% 7.75/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f13,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.75/1.50    inference(ennf_transformation,[],[f13])).
% 7.75/1.50  
% 7.75/1.50  fof(f32,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.75/1.50    inference(flattening,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f67,plain,(
% 7.75/1.50    v1_funct_1(sK4)),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    v1_funct_1(sK3)),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.75/1.50    inference(flattening,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f70,plain,(
% 7.75/1.50    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f20,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f51,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f17,plain,(
% 7.75/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f16,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.75/1.50    inference(pure_predicate_removal,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f52,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(flattening,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.75/1.50    inference(cnf_transformation,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f75,plain,(
% 7.75/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.75/1.50    inference(equality_resolution,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.75/1.50    inference(ennf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(flattening,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f71,plain,(
% 7.75/1.50    v2_funct_1(sK4)),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f18,plain,(
% 7.75/1.50    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f53,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(flattening,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f68,plain,(
% 7.75/1.50    v1_funct_2(sK4,sK1,sK2)),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f72,plain,(
% 7.75/1.50    k1_xboole_0 != sK2),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f19,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f73,plain,(
% 7.75/1.50    k2_relset_1(sK0,sK1,sK3) != sK1),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_29,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1009,plain,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_26,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1011,plain,
% 7.75/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | ~ v1_funct_1(X3)
% 7.75/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1012,plain,
% 7.75/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.75/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.75/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.50      | v1_funct_1(X5) != iProver_top
% 7.75/1.50      | v1_funct_1(X4) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2478,plain,
% 7.75/1.50      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.50      | v1_funct_1(X2) != iProver_top
% 7.75/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1011,c_1012]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_28,negated_conjecture,
% 7.75/1.50      ( v1_funct_1(sK4) ),
% 7.75/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35,plain,
% 7.75/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2641,plain,
% 7.75/1.50      ( v1_funct_1(X2) != iProver_top
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.50      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_2478,c_35]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2642,plain,
% 7.75/1.50      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_2641]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2649,plain,
% 7.75/1.50      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.75/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1009,c_2642]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_31,negated_conjecture,
% 7.75/1.50      ( v1_funct_1(sK3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_32,plain,
% 7.75/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2722,plain,
% 7.75/1.50      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_2649,c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.75/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | ~ v1_funct_1(X3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1014,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.75/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.75/1.50      | v1_funct_1(X0) != iProver_top
% 7.75/1.50      | v1_funct_1(X3) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2725,plain,
% 7.75/1.50      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 7.75/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.75/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.75/1.50      | v1_funct_1(sK4) != iProver_top
% 7.75/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2722,c_1014]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34,plain,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_37,plain,
% 7.75/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4539,plain,
% 7.75/1.50      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_2725,c_32,c_34,c_35,c_37]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1015,plain,
% 7.75/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4546,plain,
% 7.75/1.50      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_4539,c_1015]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_25,negated_conjecture,
% 7.75/1.50      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2724,plain,
% 7.75/1.50      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_2722,c_25]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4550,plain,
% 7.75/1.50      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_4546,c_2724]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | ~ v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1018,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 7.75/1.50      | v1_relat_1(X0) != iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4560,plain,
% 7.75/1.50      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 7.75/1.50      | v1_relat_1(sK4) != iProver_top
% 7.75/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_4550,c_1018]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1078,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.50      | v1_relat_1(sK4) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1132,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.75/1.50      | v1_relat_1(sK4) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1078]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1133,plain,
% 7.75/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.75/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1319,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.75/1.50      | v1_relat_1(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1320,plain,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.75/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5354,plain,
% 7.75/1.50      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_4560,c_34,c_37,c_1133,c_1320]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4,plain,
% 7.75/1.50      ( ~ v5_relat_1(X0,X1)
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.75/1.50      | ~ v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | v5_relat_1(X0,X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_349,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | r1_tarski(k2_relat_1(X3),X4)
% 7.75/1.50      | ~ v1_relat_1(X3)
% 7.75/1.50      | X0 != X3
% 7.75/1.50      | X2 != X4 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_350,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),X2)
% 7.75/1.50      | ~ v1_relat_1(X0) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_349]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_354,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(X0),X2)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_350,c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_355,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_354]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1006,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2394,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1011,c_1006]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.75/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1022,plain,
% 7.75/1.50      ( X0 = X1
% 7.75/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2593,plain,
% 7.75/1.50      ( k2_relat_1(sK4) = sK2
% 7.75/1.50      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2394,c_1022]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5359,plain,
% 7.75/1.50      ( k2_relat_1(sK4) = sK2 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5354,c_2593]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( r1_tarski(X0,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1021,plain,
% 7.75/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.75/1.50      | ~ v1_funct_1(X1)
% 7.75/1.50      | ~ v2_funct_1(X1)
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24,negated_conjecture,
% 7.75/1.50      ( v2_funct_1(sK4) ),
% 7.75/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_323,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.75/1.50      | ~ v1_funct_1(X1)
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 7.75/1.50      | sK4 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_324,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 7.75/1.50      | ~ v1_funct_1(sK4)
% 7.75/1.50      | ~ v1_relat_1(sK4)
% 7.75/1.50      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_323]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_328,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 7.75/1.50      | ~ v1_relat_1(sK4)
% 7.75/1.50      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_324,c_28]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1007,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.75/1.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.75/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_330,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.75/1.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.75/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1682,plain,
% 7.75/1.50      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.75/1.50      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1007,c_37,c_330,c_1133]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1683,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.75/1.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_1682]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1688,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1021,c_1683]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1017,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1352,plain,
% 7.75/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1011,c_1017]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5,plain,
% 7.75/1.50      ( ~ v1_relat_1(X0)
% 7.75/1.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1020,plain,
% 7.75/1.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1408,plain,
% 7.75/1.50      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1352,c_1020]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1689,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_1688,c_1408]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1016,plain,
% 7.75/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1774,plain,
% 7.75/1.50      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1011,c_1016]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_27,negated_conjecture,
% 7.75/1.50      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_444,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.50      | sK4 != X0
% 7.75/1.50      | sK2 != X2
% 7.75/1.50      | sK1 != X1
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_445,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.75/1.50      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.75/1.50      | k1_xboole_0 = sK2 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_444]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23,negated_conjecture,
% 7.75/1.50      ( k1_xboole_0 != sK2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_447,plain,
% 7.75/1.50      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_445,c_26,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1776,plain,
% 7.75/1.50      ( k1_relat_1(sK4) = sK1 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_1774,c_447]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3014,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_1689,c_1689,c_1776]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22297,plain,
% 7.75/1.50      ( k10_relat_1(sK4,sK2) = sK1 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_5359,c_3014]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2395,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1009,c_1006]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1963,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.75/1.50      | r1_tarski(X0,sK1) != iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_1776,c_1683]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2597,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2395,c_1963]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1353,plain,
% 7.75/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1009,c_1017]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6,plain,
% 7.75/1.50      ( ~ v1_relat_1(X0)
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1019,plain,
% 7.75/1.50      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 7.75/1.50      | v1_relat_1(X0) != iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1829,plain,
% 7.75/1.50      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1352,c_1019]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2276,plain,
% 7.75/1.50      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1353,c_1829]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2598,plain,
% 7.75/1.50      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_2597,c_2276]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8093,plain,
% 7.75/1.50      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_2598,c_2598,c_4550]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22462,plain,
% 7.75/1.50      ( k2_relat_1(sK3) = sK1 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_22297,c_8093]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1406,plain,
% 7.75/1.50      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1009,c_1015]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22,negated_conjecture,
% 7.75/1.50      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 7.75/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1544,plain,
% 7.75/1.50      ( k2_relat_1(sK3) != sK1 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_1406,c_22]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,[status(thm)],[c_22462,c_1544]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ General
% 7.75/1.50  
% 7.75/1.50  abstr_ref_over_cycles:                  0
% 7.75/1.50  abstr_ref_under_cycles:                 0
% 7.75/1.50  gc_basic_clause_elim:                   0
% 7.75/1.50  forced_gc_time:                         0
% 7.75/1.50  parsing_time:                           0.008
% 7.75/1.50  unif_index_cands_time:                  0.
% 7.75/1.50  unif_index_add_time:                    0.
% 7.75/1.50  orderings_time:                         0.
% 7.75/1.50  out_proof_time:                         0.011
% 7.75/1.50  total_time:                             0.736
% 7.75/1.50  num_of_symbols:                         54
% 7.75/1.50  num_of_terms:                           16003
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing
% 7.75/1.50  
% 7.75/1.50  num_of_splits:                          0
% 7.75/1.50  num_of_split_atoms:                     0
% 7.75/1.50  num_of_reused_defs:                     0
% 7.75/1.50  num_eq_ax_congr_red:                    14
% 7.75/1.50  num_of_sem_filtered_clauses:            1
% 7.75/1.50  num_of_subtypes:                        0
% 7.75/1.50  monotx_restored_types:                  0
% 7.75/1.50  sat_num_of_epr_types:                   0
% 7.75/1.50  sat_num_of_non_cyclic_types:            0
% 7.75/1.50  sat_guarded_non_collapsed_types:        0
% 7.75/1.50  num_pure_diseq_elim:                    0
% 7.75/1.50  simp_replaced_by:                       0
% 7.75/1.50  res_preprocessed:                       140
% 7.75/1.50  prep_upred:                             0
% 7.75/1.50  prep_unflattend:                        37
% 7.75/1.50  smt_new_axioms:                         0
% 7.75/1.50  pred_elim_cands:                        4
% 7.75/1.50  pred_elim:                              3
% 7.75/1.50  pred_elim_cl:                           5
% 7.75/1.50  pred_elim_cycles:                       5
% 7.75/1.50  merged_defs:                            0
% 7.75/1.50  merged_defs_ncl:                        0
% 7.75/1.50  bin_hyper_res:                          0
% 7.75/1.50  prep_cycles:                            4
% 7.75/1.50  pred_elim_time:                         0.01
% 7.75/1.50  splitting_time:                         0.
% 7.75/1.50  sem_filter_time:                        0.
% 7.75/1.50  monotx_time:                            0.
% 7.75/1.50  subtype_inf_time:                       0.
% 7.75/1.50  
% 7.75/1.50  ------ Problem properties
% 7.75/1.50  
% 7.75/1.50  clauses:                                26
% 7.75/1.50  conjectures:                            7
% 7.75/1.50  epr:                                    5
% 7.75/1.50  horn:                                   23
% 7.75/1.50  ground:                                 13
% 7.75/1.50  unary:                                  9
% 7.75/1.50  binary:                                 6
% 7.75/1.50  lits:                                   62
% 7.75/1.50  lits_eq:                                23
% 7.75/1.50  fd_pure:                                0
% 7.75/1.50  fd_pseudo:                              0
% 7.75/1.50  fd_cond:                                0
% 7.75/1.50  fd_pseudo_cond:                         1
% 7.75/1.50  ac_symbols:                             0
% 7.75/1.50  
% 7.75/1.50  ------ Propositional Solver
% 7.75/1.50  
% 7.75/1.50  prop_solver_calls:                      34
% 7.75/1.50  prop_fast_solver_calls:                 1870
% 7.75/1.50  smt_solver_calls:                       0
% 7.75/1.50  smt_fast_solver_calls:                  0
% 7.75/1.50  prop_num_of_clauses:                    9752
% 7.75/1.50  prop_preprocess_simplified:             14660
% 7.75/1.50  prop_fo_subsumed:                       338
% 7.75/1.50  prop_solver_time:                       0.
% 7.75/1.50  smt_solver_time:                        0.
% 7.75/1.50  smt_fast_solver_time:                   0.
% 7.75/1.50  prop_fast_solver_time:                  0.
% 7.75/1.50  prop_unsat_core_time:                   0.001
% 7.75/1.50  
% 7.75/1.50  ------ QBF
% 7.75/1.50  
% 7.75/1.50  qbf_q_res:                              0
% 7.75/1.50  qbf_num_tautologies:                    0
% 7.75/1.50  qbf_prep_cycles:                        0
% 7.75/1.50  
% 7.75/1.50  ------ BMC1
% 7.75/1.50  
% 7.75/1.50  bmc1_current_bound:                     -1
% 7.75/1.50  bmc1_last_solved_bound:                 -1
% 7.75/1.50  bmc1_unsat_core_size:                   -1
% 7.75/1.50  bmc1_unsat_core_parents_size:           -1
% 7.75/1.50  bmc1_merge_next_fun:                    0
% 7.75/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation
% 7.75/1.50  
% 7.75/1.50  inst_num_of_clauses:                    2781
% 7.75/1.50  inst_num_in_passive:                    356
% 7.75/1.50  inst_num_in_active:                     1716
% 7.75/1.50  inst_num_in_unprocessed:                709
% 7.75/1.50  inst_num_of_loops:                      1810
% 7.75/1.50  inst_num_of_learning_restarts:          0
% 7.75/1.50  inst_num_moves_active_passive:          88
% 7.75/1.50  inst_lit_activity:                      0
% 7.75/1.50  inst_lit_activity_moves:                0
% 7.75/1.50  inst_num_tautologies:                   0
% 7.75/1.50  inst_num_prop_implied:                  0
% 7.75/1.50  inst_num_existing_simplified:           0
% 7.75/1.50  inst_num_eq_res_simplified:             0
% 7.75/1.50  inst_num_child_elim:                    0
% 7.75/1.50  inst_num_of_dismatching_blockings:      883
% 7.75/1.50  inst_num_of_non_proper_insts:           4662
% 7.75/1.50  inst_num_of_duplicates:                 0
% 7.75/1.50  inst_inst_num_from_inst_to_res:         0
% 7.75/1.50  inst_dismatching_checking_time:         0.
% 7.75/1.50  
% 7.75/1.50  ------ Resolution
% 7.75/1.50  
% 7.75/1.50  res_num_of_clauses:                     0
% 7.75/1.50  res_num_in_passive:                     0
% 7.75/1.50  res_num_in_active:                      0
% 7.75/1.50  res_num_of_loops:                       144
% 7.75/1.50  res_forward_subset_subsumed:            523
% 7.75/1.50  res_backward_subset_subsumed:           0
% 7.75/1.50  res_forward_subsumed:                   0
% 7.75/1.50  res_backward_subsumed:                  0
% 7.75/1.50  res_forward_subsumption_resolution:     0
% 7.75/1.50  res_backward_subsumption_resolution:    0
% 7.75/1.50  res_clause_to_clause_subsumption:       2503
% 7.75/1.50  res_orphan_elimination:                 0
% 7.75/1.50  res_tautology_del:                      424
% 7.75/1.50  res_num_eq_res_simplified:              0
% 7.75/1.50  res_num_sel_changes:                    0
% 7.75/1.50  res_moves_from_active_to_pass:          0
% 7.75/1.50  
% 7.75/1.50  ------ Superposition
% 7.75/1.50  
% 7.75/1.50  sup_time_total:                         0.
% 7.75/1.50  sup_time_generating:                    0.
% 7.75/1.50  sup_time_sim_full:                      0.
% 7.75/1.50  sup_time_sim_immed:                     0.
% 7.75/1.50  
% 7.75/1.50  sup_num_of_clauses:                     1092
% 7.75/1.50  sup_num_in_active:                      341
% 7.75/1.50  sup_num_in_passive:                     751
% 7.75/1.50  sup_num_of_loops:                       361
% 7.75/1.50  sup_fw_superposition:                   560
% 7.75/1.50  sup_bw_superposition:                   665
% 7.75/1.50  sup_immediate_simplified:               438
% 7.75/1.50  sup_given_eliminated:                   1
% 7.75/1.50  comparisons_done:                       0
% 7.75/1.50  comparisons_avoided:                    6
% 7.75/1.50  
% 7.75/1.50  ------ Simplifications
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  sim_fw_subset_subsumed:                 6
% 7.75/1.50  sim_bw_subset_subsumed:                 46
% 7.75/1.50  sim_fw_subsumed:                        11
% 7.75/1.50  sim_bw_subsumed:                        0
% 7.75/1.50  sim_fw_subsumption_res:                 0
% 7.75/1.50  sim_bw_subsumption_res:                 0
% 7.75/1.50  sim_tautology_del:                      0
% 7.75/1.50  sim_eq_tautology_del:                   81
% 7.75/1.50  sim_eq_res_simp:                        0
% 7.75/1.50  sim_fw_demodulated:                     18
% 7.75/1.50  sim_bw_demodulated:                     13
% 7.75/1.50  sim_light_normalised:                   470
% 7.75/1.50  sim_joinable_taut:                      0
% 7.75/1.50  sim_joinable_simp:                      0
% 7.75/1.50  sim_ac_normalised:                      0
% 7.75/1.50  sim_smt_subsumption:                    0
% 7.75/1.50  
%------------------------------------------------------------------------------
