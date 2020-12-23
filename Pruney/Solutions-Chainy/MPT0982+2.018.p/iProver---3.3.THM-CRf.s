%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:40 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 907 expanded)
%              Number of clauses        :   94 ( 291 expanded)
%              Number of leaves         :   16 ( 219 expanded)
%              Depth                    :   21
%              Number of atoms          :  479 (6156 expanded)
%              Number of equality atoms :  211 (2083 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1005,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1007,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1010,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1011,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2626,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_1011])).

cnf(c_4321,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_2626])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4469,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4321,c_35])).

cnf(c_4470,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4469])).

cnf(c_4477,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_4470])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1008,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2616,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1008])).

cnf(c_2794,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2616,c_35])).

cnf(c_2795,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2794])).

cnf(c_2802,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_2795])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2939,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2802,c_32])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2941,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2939,c_25])).

cnf(c_4481,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4477,c_2939,c_2941])).

cnf(c_4490,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4481,c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1013,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1342,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_1013])).

cnf(c_1341,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1013])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1016,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1911,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1016])).

cnf(c_2408,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1342,c_1911])).

cnf(c_4493,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4490,c_2408])).

cnf(c_8,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_323,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_324,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_28])).

cnf(c_1003,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_330,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1129,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_1614,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_37,c_330,c_1129])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1018,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1793,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_1018])).

cnf(c_4591,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4493,c_1793])).

cnf(c_4593,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4591,c_4493])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1014,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4496,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4490,c_1014])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1294,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1295,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_4941,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4496,c_34,c_37,c_1129,c_1295])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_9])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_1002,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_2538,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1002])).

cnf(c_2706,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_1018])).

cnf(c_4946,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_4941,c_2706])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1015,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1393,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1341,c_1015])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1012,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1788,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1007,c_1012])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_441,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_443,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_26,c_23])).

cnf(c_1790,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1788,c_443])).

cnf(c_2366,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1393,c_1393,c_1790])).

cnf(c_30787,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4946,c_2366])).

cnf(c_32137,plain,
    ( k2_relat_1(sK3) = sK1
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4593,c_30787])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | r1_tarski(k2_relat_1(X0),sK1) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1551,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_1391,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1005,c_1011])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1538,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1391,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32137,c_1551,c_1538,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.57/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.57/2.00  
% 11.57/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.57/2.00  
% 11.57/2.00  ------  iProver source info
% 11.57/2.00  
% 11.57/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.57/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.57/2.00  git: non_committed_changes: false
% 11.57/2.00  git: last_make_outside_of_git: false
% 11.57/2.00  
% 11.57/2.00  ------ 
% 11.57/2.00  
% 11.57/2.00  ------ Input Options
% 11.57/2.00  
% 11.57/2.00  --out_options                           all
% 11.57/2.00  --tptp_safe_out                         true
% 11.57/2.00  --problem_path                          ""
% 11.57/2.00  --include_path                          ""
% 11.57/2.00  --clausifier                            res/vclausify_rel
% 11.57/2.00  --clausifier_options                    ""
% 11.57/2.00  --stdin                                 false
% 11.57/2.00  --stats_out                             all
% 11.57/2.00  
% 11.57/2.00  ------ General Options
% 11.57/2.00  
% 11.57/2.00  --fof                                   false
% 11.57/2.00  --time_out_real                         305.
% 11.57/2.00  --time_out_virtual                      -1.
% 11.57/2.00  --symbol_type_check                     false
% 11.57/2.00  --clausify_out                          false
% 11.57/2.00  --sig_cnt_out                           false
% 11.57/2.00  --trig_cnt_out                          false
% 11.57/2.00  --trig_cnt_out_tolerance                1.
% 11.57/2.00  --trig_cnt_out_sk_spl                   false
% 11.57/2.00  --abstr_cl_out                          false
% 11.57/2.00  
% 11.57/2.00  ------ Global Options
% 11.57/2.00  
% 11.57/2.00  --schedule                              default
% 11.57/2.00  --add_important_lit                     false
% 11.57/2.00  --prop_solver_per_cl                    1000
% 11.57/2.00  --min_unsat_core                        false
% 11.57/2.00  --soft_assumptions                      false
% 11.57/2.00  --soft_lemma_size                       3
% 11.57/2.00  --prop_impl_unit_size                   0
% 11.57/2.00  --prop_impl_unit                        []
% 11.57/2.00  --share_sel_clauses                     true
% 11.57/2.00  --reset_solvers                         false
% 11.57/2.00  --bc_imp_inh                            [conj_cone]
% 11.57/2.00  --conj_cone_tolerance                   3.
% 11.57/2.00  --extra_neg_conj                        none
% 11.57/2.00  --large_theory_mode                     true
% 11.57/2.00  --prolific_symb_bound                   200
% 11.57/2.00  --lt_threshold                          2000
% 11.57/2.00  --clause_weak_htbl                      true
% 11.57/2.00  --gc_record_bc_elim                     false
% 11.57/2.00  
% 11.57/2.00  ------ Preprocessing Options
% 11.57/2.00  
% 11.57/2.00  --preprocessing_flag                    true
% 11.57/2.00  --time_out_prep_mult                    0.1
% 11.57/2.00  --splitting_mode                        input
% 11.57/2.00  --splitting_grd                         true
% 11.57/2.00  --splitting_cvd                         false
% 11.57/2.00  --splitting_cvd_svl                     false
% 11.57/2.00  --splitting_nvd                         32
% 11.57/2.00  --sub_typing                            true
% 11.57/2.00  --prep_gs_sim                           true
% 11.57/2.00  --prep_unflatten                        true
% 11.57/2.00  --prep_res_sim                          true
% 11.57/2.00  --prep_upred                            true
% 11.57/2.00  --prep_sem_filter                       exhaustive
% 11.57/2.00  --prep_sem_filter_out                   false
% 11.57/2.00  --pred_elim                             true
% 11.57/2.00  --res_sim_input                         true
% 11.57/2.00  --eq_ax_congr_red                       true
% 11.57/2.00  --pure_diseq_elim                       true
% 11.57/2.00  --brand_transform                       false
% 11.57/2.00  --non_eq_to_eq                          false
% 11.57/2.00  --prep_def_merge                        true
% 11.57/2.00  --prep_def_merge_prop_impl              false
% 11.57/2.00  --prep_def_merge_mbd                    true
% 11.57/2.00  --prep_def_merge_tr_red                 false
% 11.57/2.00  --prep_def_merge_tr_cl                  false
% 11.57/2.00  --smt_preprocessing                     true
% 11.57/2.00  --smt_ac_axioms                         fast
% 11.57/2.00  --preprocessed_out                      false
% 11.57/2.00  --preprocessed_stats                    false
% 11.57/2.00  
% 11.57/2.00  ------ Abstraction refinement Options
% 11.57/2.00  
% 11.57/2.00  --abstr_ref                             []
% 11.57/2.00  --abstr_ref_prep                        false
% 11.57/2.00  --abstr_ref_until_sat                   false
% 11.57/2.00  --abstr_ref_sig_restrict                funpre
% 11.57/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.57/2.00  --abstr_ref_under                       []
% 11.57/2.00  
% 11.57/2.00  ------ SAT Options
% 11.57/2.00  
% 11.57/2.00  --sat_mode                              false
% 11.57/2.00  --sat_fm_restart_options                ""
% 11.57/2.00  --sat_gr_def                            false
% 11.57/2.00  --sat_epr_types                         true
% 11.57/2.00  --sat_non_cyclic_types                  false
% 11.57/2.00  --sat_finite_models                     false
% 11.57/2.00  --sat_fm_lemmas                         false
% 11.57/2.00  --sat_fm_prep                           false
% 11.57/2.00  --sat_fm_uc_incr                        true
% 11.57/2.00  --sat_out_model                         small
% 11.57/2.00  --sat_out_clauses                       false
% 11.57/2.00  
% 11.57/2.00  ------ QBF Options
% 11.57/2.00  
% 11.57/2.00  --qbf_mode                              false
% 11.57/2.00  --qbf_elim_univ                         false
% 11.57/2.00  --qbf_dom_inst                          none
% 11.57/2.00  --qbf_dom_pre_inst                      false
% 11.57/2.00  --qbf_sk_in                             false
% 11.57/2.00  --qbf_pred_elim                         true
% 11.57/2.00  --qbf_split                             512
% 11.57/2.00  
% 11.57/2.00  ------ BMC1 Options
% 11.57/2.00  
% 11.57/2.00  --bmc1_incremental                      false
% 11.57/2.00  --bmc1_axioms                           reachable_all
% 11.57/2.00  --bmc1_min_bound                        0
% 11.57/2.00  --bmc1_max_bound                        -1
% 11.57/2.00  --bmc1_max_bound_default                -1
% 11.57/2.00  --bmc1_symbol_reachability              true
% 11.57/2.00  --bmc1_property_lemmas                  false
% 11.57/2.00  --bmc1_k_induction                      false
% 11.57/2.00  --bmc1_non_equiv_states                 false
% 11.57/2.00  --bmc1_deadlock                         false
% 11.57/2.00  --bmc1_ucm                              false
% 11.57/2.00  --bmc1_add_unsat_core                   none
% 11.57/2.00  --bmc1_unsat_core_children              false
% 11.57/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.57/2.00  --bmc1_out_stat                         full
% 11.57/2.00  --bmc1_ground_init                      false
% 11.57/2.00  --bmc1_pre_inst_next_state              false
% 11.57/2.00  --bmc1_pre_inst_state                   false
% 11.57/2.00  --bmc1_pre_inst_reach_state             false
% 11.57/2.00  --bmc1_out_unsat_core                   false
% 11.57/2.00  --bmc1_aig_witness_out                  false
% 11.57/2.00  --bmc1_verbose                          false
% 11.57/2.00  --bmc1_dump_clauses_tptp                false
% 11.57/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.57/2.00  --bmc1_dump_file                        -
% 11.57/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.57/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.57/2.00  --bmc1_ucm_extend_mode                  1
% 11.57/2.00  --bmc1_ucm_init_mode                    2
% 11.57/2.00  --bmc1_ucm_cone_mode                    none
% 11.57/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.57/2.00  --bmc1_ucm_relax_model                  4
% 11.57/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.57/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.57/2.00  --bmc1_ucm_layered_model                none
% 11.57/2.00  --bmc1_ucm_max_lemma_size               10
% 11.57/2.00  
% 11.57/2.00  ------ AIG Options
% 11.57/2.00  
% 11.57/2.00  --aig_mode                              false
% 11.57/2.00  
% 11.57/2.00  ------ Instantiation Options
% 11.57/2.00  
% 11.57/2.00  --instantiation_flag                    true
% 11.57/2.00  --inst_sos_flag                         true
% 11.57/2.00  --inst_sos_phase                        true
% 11.57/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.57/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.57/2.00  --inst_lit_sel_side                     num_symb
% 11.57/2.00  --inst_solver_per_active                1400
% 11.57/2.00  --inst_solver_calls_frac                1.
% 11.57/2.00  --inst_passive_queue_type               priority_queues
% 11.57/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.57/2.00  --inst_passive_queues_freq              [25;2]
% 11.57/2.00  --inst_dismatching                      true
% 11.57/2.00  --inst_eager_unprocessed_to_passive     true
% 11.57/2.00  --inst_prop_sim_given                   true
% 11.57/2.00  --inst_prop_sim_new                     false
% 11.57/2.00  --inst_subs_new                         false
% 11.57/2.00  --inst_eq_res_simp                      false
% 11.57/2.00  --inst_subs_given                       false
% 11.57/2.00  --inst_orphan_elimination               true
% 11.57/2.00  --inst_learning_loop_flag               true
% 11.57/2.00  --inst_learning_start                   3000
% 11.57/2.00  --inst_learning_factor                  2
% 11.57/2.00  --inst_start_prop_sim_after_learn       3
% 11.57/2.00  --inst_sel_renew                        solver
% 11.57/2.00  --inst_lit_activity_flag                true
% 11.57/2.00  --inst_restr_to_given                   false
% 11.57/2.00  --inst_activity_threshold               500
% 11.57/2.00  --inst_out_proof                        true
% 11.57/2.00  
% 11.57/2.00  ------ Resolution Options
% 11.57/2.00  
% 11.57/2.00  --resolution_flag                       true
% 11.57/2.00  --res_lit_sel                           adaptive
% 11.57/2.00  --res_lit_sel_side                      none
% 11.57/2.00  --res_ordering                          kbo
% 11.57/2.00  --res_to_prop_solver                    active
% 11.57/2.00  --res_prop_simpl_new                    false
% 11.57/2.00  --res_prop_simpl_given                  true
% 11.57/2.00  --res_passive_queue_type                priority_queues
% 11.57/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.57/2.00  --res_passive_queues_freq               [15;5]
% 11.57/2.00  --res_forward_subs                      full
% 11.57/2.00  --res_backward_subs                     full
% 11.57/2.00  --res_forward_subs_resolution           true
% 11.57/2.00  --res_backward_subs_resolution          true
% 11.57/2.00  --res_orphan_elimination                true
% 11.57/2.00  --res_time_limit                        2.
% 11.57/2.00  --res_out_proof                         true
% 11.57/2.00  
% 11.57/2.00  ------ Superposition Options
% 11.57/2.00  
% 11.57/2.00  --superposition_flag                    true
% 11.57/2.00  --sup_passive_queue_type                priority_queues
% 11.57/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.57/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.57/2.00  --demod_completeness_check              fast
% 11.57/2.00  --demod_use_ground                      true
% 11.57/2.00  --sup_to_prop_solver                    passive
% 11.57/2.00  --sup_prop_simpl_new                    true
% 11.57/2.00  --sup_prop_simpl_given                  true
% 11.57/2.00  --sup_fun_splitting                     true
% 11.57/2.00  --sup_smt_interval                      50000
% 11.57/2.00  
% 11.57/2.00  ------ Superposition Simplification Setup
% 11.57/2.00  
% 11.57/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.57/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.57/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.57/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.57/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.57/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.57/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.57/2.00  --sup_immed_triv                        [TrivRules]
% 11.57/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_immed_bw_main                     []
% 11.57/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.57/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.57/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_input_bw                          []
% 11.57/2.00  
% 11.57/2.00  ------ Combination Options
% 11.57/2.00  
% 11.57/2.00  --comb_res_mult                         3
% 11.57/2.00  --comb_sup_mult                         2
% 11.57/2.00  --comb_inst_mult                        10
% 11.57/2.00  
% 11.57/2.00  ------ Debug Options
% 11.57/2.00  
% 11.57/2.00  --dbg_backtrace                         false
% 11.57/2.00  --dbg_dump_prop_clauses                 false
% 11.57/2.00  --dbg_dump_prop_clauses_file            -
% 11.57/2.00  --dbg_out_stat                          false
% 11.57/2.00  ------ Parsing...
% 11.57/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.57/2.00  
% 11.57/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.57/2.00  
% 11.57/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.57/2.00  
% 11.57/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.57/2.00  ------ Proving...
% 11.57/2.00  ------ Problem Properties 
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  clauses                                 26
% 11.57/2.00  conjectures                             7
% 11.57/2.00  EPR                                     5
% 11.57/2.00  Horn                                    23
% 11.57/2.00  unary                                   9
% 11.57/2.00  binary                                  7
% 11.57/2.00  lits                                    61
% 11.57/2.00  lits eq                                 22
% 11.57/2.00  fd_pure                                 0
% 11.57/2.00  fd_pseudo                               0
% 11.57/2.00  fd_cond                                 0
% 11.57/2.00  fd_pseudo_cond                          1
% 11.57/2.00  AC symbols                              0
% 11.57/2.00  
% 11.57/2.00  ------ Schedule dynamic 5 is on 
% 11.57/2.00  
% 11.57/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  ------ 
% 11.57/2.00  Current options:
% 11.57/2.00  ------ 
% 11.57/2.00  
% 11.57/2.00  ------ Input Options
% 11.57/2.00  
% 11.57/2.00  --out_options                           all
% 11.57/2.00  --tptp_safe_out                         true
% 11.57/2.00  --problem_path                          ""
% 11.57/2.00  --include_path                          ""
% 11.57/2.00  --clausifier                            res/vclausify_rel
% 11.57/2.00  --clausifier_options                    ""
% 11.57/2.00  --stdin                                 false
% 11.57/2.00  --stats_out                             all
% 11.57/2.00  
% 11.57/2.00  ------ General Options
% 11.57/2.00  
% 11.57/2.00  --fof                                   false
% 11.57/2.00  --time_out_real                         305.
% 11.57/2.00  --time_out_virtual                      -1.
% 11.57/2.00  --symbol_type_check                     false
% 11.57/2.00  --clausify_out                          false
% 11.57/2.00  --sig_cnt_out                           false
% 11.57/2.00  --trig_cnt_out                          false
% 11.57/2.00  --trig_cnt_out_tolerance                1.
% 11.57/2.00  --trig_cnt_out_sk_spl                   false
% 11.57/2.00  --abstr_cl_out                          false
% 11.57/2.00  
% 11.57/2.00  ------ Global Options
% 11.57/2.00  
% 11.57/2.00  --schedule                              default
% 11.57/2.00  --add_important_lit                     false
% 11.57/2.00  --prop_solver_per_cl                    1000
% 11.57/2.00  --min_unsat_core                        false
% 11.57/2.00  --soft_assumptions                      false
% 11.57/2.00  --soft_lemma_size                       3
% 11.57/2.00  --prop_impl_unit_size                   0
% 11.57/2.00  --prop_impl_unit                        []
% 11.57/2.00  --share_sel_clauses                     true
% 11.57/2.00  --reset_solvers                         false
% 11.57/2.00  --bc_imp_inh                            [conj_cone]
% 11.57/2.00  --conj_cone_tolerance                   3.
% 11.57/2.00  --extra_neg_conj                        none
% 11.57/2.00  --large_theory_mode                     true
% 11.57/2.00  --prolific_symb_bound                   200
% 11.57/2.00  --lt_threshold                          2000
% 11.57/2.00  --clause_weak_htbl                      true
% 11.57/2.00  --gc_record_bc_elim                     false
% 11.57/2.00  
% 11.57/2.00  ------ Preprocessing Options
% 11.57/2.00  
% 11.57/2.00  --preprocessing_flag                    true
% 11.57/2.00  --time_out_prep_mult                    0.1
% 11.57/2.00  --splitting_mode                        input
% 11.57/2.00  --splitting_grd                         true
% 11.57/2.00  --splitting_cvd                         false
% 11.57/2.00  --splitting_cvd_svl                     false
% 11.57/2.00  --splitting_nvd                         32
% 11.57/2.00  --sub_typing                            true
% 11.57/2.00  --prep_gs_sim                           true
% 11.57/2.00  --prep_unflatten                        true
% 11.57/2.00  --prep_res_sim                          true
% 11.57/2.00  --prep_upred                            true
% 11.57/2.00  --prep_sem_filter                       exhaustive
% 11.57/2.00  --prep_sem_filter_out                   false
% 11.57/2.00  --pred_elim                             true
% 11.57/2.00  --res_sim_input                         true
% 11.57/2.00  --eq_ax_congr_red                       true
% 11.57/2.00  --pure_diseq_elim                       true
% 11.57/2.00  --brand_transform                       false
% 11.57/2.00  --non_eq_to_eq                          false
% 11.57/2.00  --prep_def_merge                        true
% 11.57/2.00  --prep_def_merge_prop_impl              false
% 11.57/2.00  --prep_def_merge_mbd                    true
% 11.57/2.00  --prep_def_merge_tr_red                 false
% 11.57/2.00  --prep_def_merge_tr_cl                  false
% 11.57/2.00  --smt_preprocessing                     true
% 11.57/2.00  --smt_ac_axioms                         fast
% 11.57/2.00  --preprocessed_out                      false
% 11.57/2.00  --preprocessed_stats                    false
% 11.57/2.00  
% 11.57/2.00  ------ Abstraction refinement Options
% 11.57/2.00  
% 11.57/2.00  --abstr_ref                             []
% 11.57/2.00  --abstr_ref_prep                        false
% 11.57/2.00  --abstr_ref_until_sat                   false
% 11.57/2.00  --abstr_ref_sig_restrict                funpre
% 11.57/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.57/2.00  --abstr_ref_under                       []
% 11.57/2.00  
% 11.57/2.00  ------ SAT Options
% 11.57/2.00  
% 11.57/2.00  --sat_mode                              false
% 11.57/2.00  --sat_fm_restart_options                ""
% 11.57/2.00  --sat_gr_def                            false
% 11.57/2.00  --sat_epr_types                         true
% 11.57/2.00  --sat_non_cyclic_types                  false
% 11.57/2.00  --sat_finite_models                     false
% 11.57/2.00  --sat_fm_lemmas                         false
% 11.57/2.00  --sat_fm_prep                           false
% 11.57/2.00  --sat_fm_uc_incr                        true
% 11.57/2.00  --sat_out_model                         small
% 11.57/2.00  --sat_out_clauses                       false
% 11.57/2.00  
% 11.57/2.00  ------ QBF Options
% 11.57/2.00  
% 11.57/2.00  --qbf_mode                              false
% 11.57/2.00  --qbf_elim_univ                         false
% 11.57/2.00  --qbf_dom_inst                          none
% 11.57/2.00  --qbf_dom_pre_inst                      false
% 11.57/2.00  --qbf_sk_in                             false
% 11.57/2.00  --qbf_pred_elim                         true
% 11.57/2.00  --qbf_split                             512
% 11.57/2.00  
% 11.57/2.00  ------ BMC1 Options
% 11.57/2.00  
% 11.57/2.00  --bmc1_incremental                      false
% 11.57/2.00  --bmc1_axioms                           reachable_all
% 11.57/2.00  --bmc1_min_bound                        0
% 11.57/2.00  --bmc1_max_bound                        -1
% 11.57/2.00  --bmc1_max_bound_default                -1
% 11.57/2.00  --bmc1_symbol_reachability              true
% 11.57/2.00  --bmc1_property_lemmas                  false
% 11.57/2.00  --bmc1_k_induction                      false
% 11.57/2.00  --bmc1_non_equiv_states                 false
% 11.57/2.00  --bmc1_deadlock                         false
% 11.57/2.00  --bmc1_ucm                              false
% 11.57/2.00  --bmc1_add_unsat_core                   none
% 11.57/2.00  --bmc1_unsat_core_children              false
% 11.57/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.57/2.00  --bmc1_out_stat                         full
% 11.57/2.00  --bmc1_ground_init                      false
% 11.57/2.00  --bmc1_pre_inst_next_state              false
% 11.57/2.00  --bmc1_pre_inst_state                   false
% 11.57/2.00  --bmc1_pre_inst_reach_state             false
% 11.57/2.00  --bmc1_out_unsat_core                   false
% 11.57/2.00  --bmc1_aig_witness_out                  false
% 11.57/2.00  --bmc1_verbose                          false
% 11.57/2.00  --bmc1_dump_clauses_tptp                false
% 11.57/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.57/2.00  --bmc1_dump_file                        -
% 11.57/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.57/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.57/2.00  --bmc1_ucm_extend_mode                  1
% 11.57/2.00  --bmc1_ucm_init_mode                    2
% 11.57/2.00  --bmc1_ucm_cone_mode                    none
% 11.57/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.57/2.00  --bmc1_ucm_relax_model                  4
% 11.57/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.57/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.57/2.00  --bmc1_ucm_layered_model                none
% 11.57/2.00  --bmc1_ucm_max_lemma_size               10
% 11.57/2.00  
% 11.57/2.00  ------ AIG Options
% 11.57/2.00  
% 11.57/2.00  --aig_mode                              false
% 11.57/2.00  
% 11.57/2.00  ------ Instantiation Options
% 11.57/2.00  
% 11.57/2.00  --instantiation_flag                    true
% 11.57/2.00  --inst_sos_flag                         true
% 11.57/2.00  --inst_sos_phase                        true
% 11.57/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.57/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.57/2.00  --inst_lit_sel_side                     none
% 11.57/2.00  --inst_solver_per_active                1400
% 11.57/2.00  --inst_solver_calls_frac                1.
% 11.57/2.00  --inst_passive_queue_type               priority_queues
% 11.57/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.57/2.00  --inst_passive_queues_freq              [25;2]
% 11.57/2.00  --inst_dismatching                      true
% 11.57/2.00  --inst_eager_unprocessed_to_passive     true
% 11.57/2.00  --inst_prop_sim_given                   true
% 11.57/2.00  --inst_prop_sim_new                     false
% 11.57/2.00  --inst_subs_new                         false
% 11.57/2.00  --inst_eq_res_simp                      false
% 11.57/2.00  --inst_subs_given                       false
% 11.57/2.00  --inst_orphan_elimination               true
% 11.57/2.00  --inst_learning_loop_flag               true
% 11.57/2.00  --inst_learning_start                   3000
% 11.57/2.00  --inst_learning_factor                  2
% 11.57/2.00  --inst_start_prop_sim_after_learn       3
% 11.57/2.00  --inst_sel_renew                        solver
% 11.57/2.00  --inst_lit_activity_flag                true
% 11.57/2.00  --inst_restr_to_given                   false
% 11.57/2.00  --inst_activity_threshold               500
% 11.57/2.00  --inst_out_proof                        true
% 11.57/2.00  
% 11.57/2.00  ------ Resolution Options
% 11.57/2.00  
% 11.57/2.00  --resolution_flag                       false
% 11.57/2.00  --res_lit_sel                           adaptive
% 11.57/2.00  --res_lit_sel_side                      none
% 11.57/2.00  --res_ordering                          kbo
% 11.57/2.00  --res_to_prop_solver                    active
% 11.57/2.00  --res_prop_simpl_new                    false
% 11.57/2.00  --res_prop_simpl_given                  true
% 11.57/2.00  --res_passive_queue_type                priority_queues
% 11.57/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.57/2.00  --res_passive_queues_freq               [15;5]
% 11.57/2.00  --res_forward_subs                      full
% 11.57/2.00  --res_backward_subs                     full
% 11.57/2.00  --res_forward_subs_resolution           true
% 11.57/2.00  --res_backward_subs_resolution          true
% 11.57/2.00  --res_orphan_elimination                true
% 11.57/2.00  --res_time_limit                        2.
% 11.57/2.00  --res_out_proof                         true
% 11.57/2.00  
% 11.57/2.00  ------ Superposition Options
% 11.57/2.00  
% 11.57/2.00  --superposition_flag                    true
% 11.57/2.00  --sup_passive_queue_type                priority_queues
% 11.57/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.57/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.57/2.00  --demod_completeness_check              fast
% 11.57/2.00  --demod_use_ground                      true
% 11.57/2.00  --sup_to_prop_solver                    passive
% 11.57/2.00  --sup_prop_simpl_new                    true
% 11.57/2.00  --sup_prop_simpl_given                  true
% 11.57/2.00  --sup_fun_splitting                     true
% 11.57/2.00  --sup_smt_interval                      50000
% 11.57/2.00  
% 11.57/2.00  ------ Superposition Simplification Setup
% 11.57/2.00  
% 11.57/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.57/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.57/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.57/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.57/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.57/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.57/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.57/2.00  --sup_immed_triv                        [TrivRules]
% 11.57/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_immed_bw_main                     []
% 11.57/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.57/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.57/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/2.00  --sup_input_bw                          []
% 11.57/2.00  
% 11.57/2.00  ------ Combination Options
% 11.57/2.00  
% 11.57/2.00  --comb_res_mult                         3
% 11.57/2.00  --comb_sup_mult                         2
% 11.57/2.00  --comb_inst_mult                        10
% 11.57/2.00  
% 11.57/2.00  ------ Debug Options
% 11.57/2.00  
% 11.57/2.00  --dbg_backtrace                         false
% 11.57/2.00  --dbg_dump_prop_clauses                 false
% 11.57/2.00  --dbg_dump_prop_clauses_file            -
% 11.57/2.00  --dbg_out_stat                          false
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  ------ Proving...
% 11.57/2.00  
% 11.57/2.00  
% 11.57/2.00  % SZS status Theorem for theBenchmark.p
% 11.57/2.00  
% 11.57/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.57/2.00  
% 11.57/2.00  fof(f14,conjecture,(
% 11.57/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f15,negated_conjecture,(
% 11.57/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.57/2.00    inference(negated_conjecture,[],[f14])).
% 11.57/2.00  
% 11.57/2.00  fof(f33,plain,(
% 11.57/2.00    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.57/2.00    inference(ennf_transformation,[],[f15])).
% 11.57/2.00  
% 11.57/2.00  fof(f34,plain,(
% 11.57/2.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.57/2.00    inference(flattening,[],[f33])).
% 11.57/2.00  
% 11.57/2.00  fof(f40,plain,(
% 11.57/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 11.57/2.00    introduced(choice_axiom,[])).
% 11.57/2.00  
% 11.57/2.00  fof(f39,plain,(
% 11.57/2.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.57/2.00    introduced(choice_axiom,[])).
% 11.57/2.00  
% 11.57/2.00  fof(f41,plain,(
% 11.57/2.00    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.57/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39])).
% 11.57/2.00  
% 11.57/2.00  fof(f66,plain,(
% 11.57/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f69,plain,(
% 11.57/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f12,axiom,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f29,plain,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.57/2.00    inference(ennf_transformation,[],[f12])).
% 11.57/2.00  
% 11.57/2.00  fof(f30,plain,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.57/2.00    inference(flattening,[],[f29])).
% 11.57/2.00  
% 11.57/2.00  fof(f62,plain,(
% 11.57/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f30])).
% 11.57/2.00  
% 11.57/2.00  fof(f10,axiom,(
% 11.57/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f26,plain,(
% 11.57/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.00    inference(ennf_transformation,[],[f10])).
% 11.57/2.00  
% 11.57/2.00  fof(f54,plain,(
% 11.57/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/2.00    inference(cnf_transformation,[],[f26])).
% 11.57/2.00  
% 11.57/2.00  fof(f67,plain,(
% 11.57/2.00    v1_funct_1(sK4)),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f13,axiom,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f31,plain,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.57/2.00    inference(ennf_transformation,[],[f13])).
% 11.57/2.00  
% 11.57/2.00  fof(f32,plain,(
% 11.57/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.57/2.00    inference(flattening,[],[f31])).
% 11.57/2.00  
% 11.57/2.00  fof(f63,plain,(
% 11.57/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f32])).
% 11.57/2.00  
% 11.57/2.00  fof(f64,plain,(
% 11.57/2.00    v1_funct_1(sK3)),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f70,plain,(
% 11.57/2.00    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f7,axiom,(
% 11.57/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f23,plain,(
% 11.57/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.00    inference(ennf_transformation,[],[f7])).
% 11.57/2.00  
% 11.57/2.00  fof(f51,plain,(
% 11.57/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/2.00    inference(cnf_transformation,[],[f23])).
% 11.57/2.00  
% 11.57/2.00  fof(f3,axiom,(
% 11.57/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f18,plain,(
% 11.57/2.00    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.57/2.00    inference(ennf_transformation,[],[f3])).
% 11.57/2.00  
% 11.57/2.00  fof(f47,plain,(
% 11.57/2.00    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f18])).
% 11.57/2.00  
% 11.57/2.00  fof(f6,axiom,(
% 11.57/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f21,plain,(
% 11.57/2.00    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.57/2.00    inference(ennf_transformation,[],[f6])).
% 11.57/2.00  
% 11.57/2.00  fof(f22,plain,(
% 11.57/2.00    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.57/2.00    inference(flattening,[],[f21])).
% 11.57/2.00  
% 11.57/2.00  fof(f50,plain,(
% 11.57/2.00    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f22])).
% 11.57/2.00  
% 11.57/2.00  fof(f71,plain,(
% 11.57/2.00    v2_funct_1(sK4)),
% 11.57/2.00    inference(cnf_transformation,[],[f41])).
% 11.57/2.00  
% 11.57/2.00  fof(f1,axiom,(
% 11.57/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f35,plain,(
% 11.57/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.57/2.00    inference(nnf_transformation,[],[f1])).
% 11.57/2.00  
% 11.57/2.00  fof(f36,plain,(
% 11.57/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.57/2.00    inference(flattening,[],[f35])).
% 11.57/2.00  
% 11.57/2.00  fof(f44,plain,(
% 11.57/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f36])).
% 11.57/2.00  
% 11.57/2.00  fof(f5,axiom,(
% 11.57/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f20,plain,(
% 11.57/2.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.57/2.00    inference(ennf_transformation,[],[f5])).
% 11.57/2.00  
% 11.57/2.00  fof(f49,plain,(
% 11.57/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.57/2.00    inference(cnf_transformation,[],[f20])).
% 11.57/2.00  
% 11.57/2.00  fof(f2,axiom,(
% 11.57/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.57/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.00  
% 11.57/2.00  fof(f17,plain,(
% 11.57/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.57/2.00    inference(ennf_transformation,[],[f2])).
% 11.57/2.00  
% 11.57/2.00  fof(f37,plain,(
% 11.57/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.57/2.00    inference(nnf_transformation,[],[f17])).
% 11.57/2.01  
% 11.57/2.01  fof(f45,plain,(
% 11.57/2.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.57/2.01    inference(cnf_transformation,[],[f37])).
% 11.57/2.01  
% 11.57/2.01  fof(f8,axiom,(
% 11.57/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.57/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.01  
% 11.57/2.01  fof(f16,plain,(
% 11.57/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.57/2.01    inference(pure_predicate_removal,[],[f8])).
% 11.57/2.01  
% 11.57/2.01  fof(f24,plain,(
% 11.57/2.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.01    inference(ennf_transformation,[],[f16])).
% 11.57/2.01  
% 11.57/2.01  fof(f52,plain,(
% 11.57/2.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/2.01    inference(cnf_transformation,[],[f24])).
% 11.57/2.01  
% 11.57/2.01  fof(f4,axiom,(
% 11.57/2.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 11.57/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.01  
% 11.57/2.01  fof(f19,plain,(
% 11.57/2.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 11.57/2.01    inference(ennf_transformation,[],[f4])).
% 11.57/2.01  
% 11.57/2.01  fof(f48,plain,(
% 11.57/2.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.57/2.01    inference(cnf_transformation,[],[f19])).
% 11.57/2.01  
% 11.57/2.01  fof(f9,axiom,(
% 11.57/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.57/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.01  
% 11.57/2.01  fof(f25,plain,(
% 11.57/2.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.01    inference(ennf_transformation,[],[f9])).
% 11.57/2.01  
% 11.57/2.01  fof(f53,plain,(
% 11.57/2.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/2.01    inference(cnf_transformation,[],[f25])).
% 11.57/2.01  
% 11.57/2.01  fof(f11,axiom,(
% 11.57/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.57/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.57/2.01  
% 11.57/2.01  fof(f27,plain,(
% 11.57/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.01    inference(ennf_transformation,[],[f11])).
% 11.57/2.01  
% 11.57/2.01  fof(f28,plain,(
% 11.57/2.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.01    inference(flattening,[],[f27])).
% 11.57/2.01  
% 11.57/2.01  fof(f38,plain,(
% 11.57/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/2.01    inference(nnf_transformation,[],[f28])).
% 11.57/2.01  
% 11.57/2.01  fof(f55,plain,(
% 11.57/2.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/2.01    inference(cnf_transformation,[],[f38])).
% 11.57/2.01  
% 11.57/2.01  fof(f68,plain,(
% 11.57/2.01    v1_funct_2(sK4,sK1,sK2)),
% 11.57/2.01    inference(cnf_transformation,[],[f41])).
% 11.57/2.01  
% 11.57/2.01  fof(f72,plain,(
% 11.57/2.01    k1_xboole_0 != sK2),
% 11.57/2.01    inference(cnf_transformation,[],[f41])).
% 11.57/2.01  
% 11.57/2.01  fof(f73,plain,(
% 11.57/2.01    k2_relset_1(sK0,sK1,sK3) != sK1),
% 11.57/2.01    inference(cnf_transformation,[],[f41])).
% 11.57/2.01  
% 11.57/2.01  cnf(c_29,negated_conjecture,
% 11.57/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.57/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1005,plain,
% 11.57/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_26,negated_conjecture,
% 11.57/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.57/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1007,plain,
% 11.57/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_19,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.57/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.57/2.01      | ~ v1_funct_1(X0)
% 11.57/2.01      | ~ v1_funct_1(X3) ),
% 11.57/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1010,plain,
% 11.57/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.57/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.57/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.57/2.01      | v1_funct_1(X0) != iProver_top
% 11.57/2.01      | v1_funct_1(X3) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_12,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1011,plain,
% 11.57/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2626,plain,
% 11.57/2.01      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 11.57/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 11.57/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 11.57/2.01      | v1_funct_1(X5) != iProver_top
% 11.57/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1010,c_1011]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4321,plain,
% 11.57/2.01      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | v1_funct_1(X2) != iProver_top
% 11.57/2.01      | v1_funct_1(sK4) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1007,c_2626]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_28,negated_conjecture,
% 11.57/2.01      ( v1_funct_1(sK4) ),
% 11.57/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_35,plain,
% 11.57/2.01      ( v1_funct_1(sK4) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4469,plain,
% 11.57/2.01      ( v1_funct_1(X2) != iProver_top
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_4321,c_35]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4470,plain,
% 11.57/2.01      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.57/2.01      inference(renaming,[status(thm)],[c_4469]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4477,plain,
% 11.57/2.01      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 11.57/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1005,c_4470]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_21,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.57/2.01      | ~ v1_funct_1(X0)
% 11.57/2.01      | ~ v1_funct_1(X3)
% 11.57/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1008,plain,
% 11.57/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.57/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.57/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | v1_funct_1(X5) != iProver_top
% 11.57/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2616,plain,
% 11.57/2.01      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | v1_funct_1(X2) != iProver_top
% 11.57/2.01      | v1_funct_1(sK4) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1007,c_1008]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2794,plain,
% 11.57/2.01      ( v1_funct_1(X2) != iProver_top
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_2616,c_35]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2795,plain,
% 11.57/2.01      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.57/2.01      inference(renaming,[status(thm)],[c_2794]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2802,plain,
% 11.57/2.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.57/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1005,c_2795]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_31,negated_conjecture,
% 11.57/2.01      ( v1_funct_1(sK3) ),
% 11.57/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_32,plain,
% 11.57/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2939,plain,
% 11.57/2.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_2802,c_32]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_25,negated_conjecture,
% 11.57/2.01      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 11.57/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2941,plain,
% 11.57/2.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 11.57/2.01      inference(demodulation,[status(thm)],[c_2939,c_25]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4481,plain,
% 11.57/2.01      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 11.57/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.57/2.01      inference(light_normalisation,[status(thm)],[c_4477,c_2939,c_2941]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4490,plain,
% 11.57/2.01      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_4481,c_32]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_9,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | v1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1013,plain,
% 11.57/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.57/2.01      | v1_relat_1(X0) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1342,plain,
% 11.57/2.01      ( v1_relat_1(sK3) = iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1005,c_1013]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1341,plain,
% 11.57/2.01      ( v1_relat_1(sK4) = iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1007,c_1013]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_5,plain,
% 11.57/2.01      ( ~ v1_relat_1(X0)
% 11.57/2.01      | ~ v1_relat_1(X1)
% 11.57/2.01      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 11.57/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1016,plain,
% 11.57/2.01      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 11.57/2.01      | v1_relat_1(X0) != iProver_top
% 11.57/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1911,plain,
% 11.57/2.01      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 11.57/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1341,c_1016]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2408,plain,
% 11.57/2.01      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1342,c_1911]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4493,plain,
% 11.57/2.01      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 11.57/2.01      inference(demodulation,[status(thm)],[c_4490,c_2408]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_8,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 11.57/2.01      | ~ v1_funct_1(X0)
% 11.57/2.01      | ~ v2_funct_1(X0)
% 11.57/2.01      | ~ v1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_24,negated_conjecture,
% 11.57/2.01      ( v2_funct_1(sK4) ),
% 11.57/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_323,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 11.57/2.01      | ~ v1_funct_1(X0)
% 11.57/2.01      | ~ v1_relat_1(X0)
% 11.57/2.01      | sK4 != X0 ),
% 11.57/2.01      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_324,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
% 11.57/2.01      | ~ v1_funct_1(sK4)
% 11.57/2.01      | ~ v1_relat_1(sK4) ),
% 11.57/2.01      inference(unflattening,[status(thm)],[c_323]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_328,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
% 11.57/2.01      | ~ v1_relat_1(sK4) ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_324,c_28]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1003,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
% 11.57/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_37,plain,
% 11.57/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_330,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
% 11.57/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1074,plain,
% 11.57/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.57/2.01      | v1_relat_1(sK4) ),
% 11.57/2.01      inference(instantiation,[status(thm)],[c_9]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1128,plain,
% 11.57/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.57/2.01      | v1_relat_1(sK4) ),
% 11.57/2.01      inference(instantiation,[status(thm)],[c_1074]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1129,plain,
% 11.57/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.57/2.01      | v1_relat_1(sK4) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1614,plain,
% 11.57/2.01      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_1003,c_37,c_330,c_1129]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_0,plain,
% 11.57/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.57/2.01      inference(cnf_transformation,[],[f44]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1018,plain,
% 11.57/2.01      ( X0 = X1
% 11.57/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.57/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1793,plain,
% 11.57/2.01      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 11.57/2.01      | r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0))) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1614,c_1018]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4591,plain,
% 11.57/2.01      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
% 11.57/2.01      | r1_tarski(k2_relat_1(sK3),k10_relat_1(sK4,sK2)) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_4493,c_1793]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4593,plain,
% 11.57/2.01      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3)
% 11.57/2.01      | r1_tarski(k2_relat_1(sK3),k10_relat_1(sK4,sK2)) != iProver_top ),
% 11.57/2.01      inference(demodulation,[status(thm)],[c_4591,c_4493]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_7,plain,
% 11.57/2.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.57/2.01      | ~ v1_relat_1(X1)
% 11.57/2.01      | ~ v1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1014,plain,
% 11.57/2.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.57/2.01      | v1_relat_1(X0) != iProver_top
% 11.57/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4496,plain,
% 11.57/2.01      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 11.57/2.01      | v1_relat_1(sK4) != iProver_top
% 11.57/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_4490,c_1014]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_34,plain,
% 11.57/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1294,plain,
% 11.57/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.57/2.01      | v1_relat_1(sK3) ),
% 11.57/2.01      inference(instantiation,[status(thm)],[c_9]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1295,plain,
% 11.57/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.57/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4941,plain,
% 11.57/2.01      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_4496,c_34,c_37,c_1129,c_1295]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4,plain,
% 11.57/2.01      ( ~ v5_relat_1(X0,X1)
% 11.57/2.01      | r1_tarski(k2_relat_1(X0),X1)
% 11.57/2.01      | ~ v1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f45]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_10,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | v5_relat_1(X0,X2) ),
% 11.57/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_345,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | r1_tarski(k2_relat_1(X3),X4)
% 11.57/2.01      | ~ v1_relat_1(X3)
% 11.57/2.01      | X0 != X3
% 11.57/2.01      | X2 != X4 ),
% 11.57/2.01      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_346,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | r1_tarski(k2_relat_1(X0),X2)
% 11.57/2.01      | ~ v1_relat_1(X0) ),
% 11.57/2.01      inference(unflattening,[status(thm)],[c_345]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_350,plain,
% 11.57/2.01      ( r1_tarski(k2_relat_1(X0),X2)
% 11.57/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_346,c_9]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_351,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.57/2.01      inference(renaming,[status(thm)],[c_350]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1002,plain,
% 11.57/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.57/2.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2538,plain,
% 11.57/2.01      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1007,c_1002]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2706,plain,
% 11.57/2.01      ( k2_relat_1(sK4) = sK2
% 11.57/2.01      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_2538,c_1018]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_4946,plain,
% 11.57/2.01      ( k2_relat_1(sK4) = sK2 ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_4941,c_2706]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_6,plain,
% 11.57/2.01      ( ~ v1_relat_1(X0)
% 11.57/2.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f48]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1015,plain,
% 11.57/2.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 11.57/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1393,plain,
% 11.57/2.01      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1341,c_1015]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_11,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.57/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1012,plain,
% 11.57/2.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.57/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1788,plain,
% 11.57/2.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1007,c_1012]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_18,plain,
% 11.57/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.57/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.57/2.01      | k1_xboole_0 = X2 ),
% 11.57/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_27,negated_conjecture,
% 11.57/2.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 11.57/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_440,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.57/2.01      | sK4 != X0
% 11.57/2.01      | sK2 != X2
% 11.57/2.01      | sK1 != X1
% 11.57/2.01      | k1_xboole_0 = X2 ),
% 11.57/2.01      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_441,plain,
% 11.57/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.57/2.01      | k1_relset_1(sK1,sK2,sK4) = sK1
% 11.57/2.01      | k1_xboole_0 = sK2 ),
% 11.57/2.01      inference(unflattening,[status(thm)],[c_440]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_23,negated_conjecture,
% 11.57/2.01      ( k1_xboole_0 != sK2 ),
% 11.57/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_443,plain,
% 11.57/2.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 11.57/2.01      inference(global_propositional_subsumption,
% 11.57/2.01                [status(thm)],
% 11.57/2.01                [c_441,c_26,c_23]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1790,plain,
% 11.57/2.01      ( k1_relat_1(sK4) = sK1 ),
% 11.57/2.01      inference(light_normalisation,[status(thm)],[c_1788,c_443]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_2366,plain,
% 11.57/2.01      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 11.57/2.01      inference(light_normalisation,[status(thm)],[c_1393,c_1393,c_1790]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_30787,plain,
% 11.57/2.01      ( k10_relat_1(sK4,sK2) = sK1 ),
% 11.57/2.01      inference(demodulation,[status(thm)],[c_4946,c_2366]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_32137,plain,
% 11.57/2.01      ( k2_relat_1(sK3) = sK1
% 11.57/2.01      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
% 11.57/2.01      inference(light_normalisation,[status(thm)],[c_4593,c_30787]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1268,plain,
% 11.57/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.57/2.01      | r1_tarski(k2_relat_1(X0),sK1) ),
% 11.57/2.01      inference(instantiation,[status(thm)],[c_351]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1550,plain,
% 11.57/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.57/2.01      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 11.57/2.01      inference(instantiation,[status(thm)],[c_1268]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1551,plain,
% 11.57/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.57/2.01      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 11.57/2.01      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1391,plain,
% 11.57/2.01      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 11.57/2.01      inference(superposition,[status(thm)],[c_1005,c_1011]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_22,negated_conjecture,
% 11.57/2.01      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 11.57/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(c_1538,plain,
% 11.57/2.01      ( k2_relat_1(sK3) != sK1 ),
% 11.57/2.01      inference(demodulation,[status(thm)],[c_1391,c_22]) ).
% 11.57/2.01  
% 11.57/2.01  cnf(contradiction,plain,
% 11.57/2.01      ( $false ),
% 11.57/2.01      inference(minisat,[status(thm)],[c_32137,c_1551,c_1538,c_34]) ).
% 11.57/2.01  
% 11.57/2.01  
% 11.57/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.57/2.01  
% 11.57/2.01  ------                               Statistics
% 11.57/2.01  
% 11.57/2.01  ------ General
% 11.57/2.01  
% 11.57/2.01  abstr_ref_over_cycles:                  0
% 11.57/2.01  abstr_ref_under_cycles:                 0
% 11.57/2.01  gc_basic_clause_elim:                   0
% 11.57/2.01  forced_gc_time:                         0
% 11.57/2.01  parsing_time:                           0.008
% 11.57/2.01  unif_index_cands_time:                  0.
% 11.57/2.01  unif_index_add_time:                    0.
% 11.57/2.01  orderings_time:                         0.
% 11.57/2.01  out_proof_time:                         0.014
% 11.57/2.01  total_time:                             1.041
% 11.57/2.01  num_of_symbols:                         54
% 11.57/2.01  num_of_terms:                           26952
% 11.57/2.01  
% 11.57/2.01  ------ Preprocessing
% 11.57/2.01  
% 11.57/2.01  num_of_splits:                          0
% 11.57/2.01  num_of_split_atoms:                     0
% 11.57/2.01  num_of_reused_defs:                     0
% 11.57/2.01  num_eq_ax_congr_red:                    16
% 11.57/2.01  num_of_sem_filtered_clauses:            1
% 11.57/2.01  num_of_subtypes:                        0
% 11.57/2.01  monotx_restored_types:                  0
% 11.57/2.01  sat_num_of_epr_types:                   0
% 11.57/2.01  sat_num_of_non_cyclic_types:            0
% 11.57/2.01  sat_guarded_non_collapsed_types:        0
% 11.57/2.01  num_pure_diseq_elim:                    0
% 11.57/2.01  simp_replaced_by:                       0
% 11.57/2.01  res_preprocessed:                       138
% 11.57/2.01  prep_upred:                             0
% 11.57/2.01  prep_unflattend:                        37
% 11.57/2.01  smt_new_axioms:                         0
% 11.57/2.01  pred_elim_cands:                        4
% 11.57/2.01  pred_elim:                              3
% 11.57/2.01  pred_elim_cl:                           5
% 11.57/2.01  pred_elim_cycles:                       5
% 11.57/2.01  merged_defs:                            0
% 11.57/2.01  merged_defs_ncl:                        0
% 11.57/2.01  bin_hyper_res:                          0
% 11.57/2.01  prep_cycles:                            4
% 11.57/2.01  pred_elim_time:                         0.003
% 11.57/2.01  splitting_time:                         0.
% 11.57/2.01  sem_filter_time:                        0.
% 11.57/2.01  monotx_time:                            0.
% 11.57/2.01  subtype_inf_time:                       0.
% 11.57/2.01  
% 11.57/2.01  ------ Problem properties
% 11.57/2.01  
% 11.57/2.01  clauses:                                26
% 11.57/2.01  conjectures:                            7
% 11.57/2.01  epr:                                    5
% 11.57/2.01  horn:                                   23
% 11.57/2.01  ground:                                 13
% 11.57/2.01  unary:                                  9
% 11.57/2.01  binary:                                 7
% 11.57/2.01  lits:                                   61
% 11.57/2.01  lits_eq:                                22
% 11.57/2.01  fd_pure:                                0
% 11.57/2.01  fd_pseudo:                              0
% 11.57/2.01  fd_cond:                                0
% 11.57/2.01  fd_pseudo_cond:                         1
% 11.57/2.01  ac_symbols:                             0
% 11.57/2.01  
% 11.57/2.01  ------ Propositional Solver
% 11.57/2.01  
% 11.57/2.01  prop_solver_calls:                      36
% 11.57/2.01  prop_fast_solver_calls:                 2577
% 11.57/2.01  smt_solver_calls:                       0
% 11.57/2.01  smt_fast_solver_calls:                  0
% 11.57/2.01  prop_num_of_clauses:                    15236
% 11.57/2.01  prop_preprocess_simplified:             17938
% 11.57/2.01  prop_fo_subsumed:                       622
% 11.57/2.01  prop_solver_time:                       0.
% 11.57/2.01  smt_solver_time:                        0.
% 11.57/2.01  smt_fast_solver_time:                   0.
% 11.57/2.01  prop_fast_solver_time:                  0.
% 11.57/2.01  prop_unsat_core_time:                   0.002
% 11.57/2.01  
% 11.57/2.01  ------ QBF
% 11.57/2.01  
% 11.57/2.01  qbf_q_res:                              0
% 11.57/2.01  qbf_num_tautologies:                    0
% 11.57/2.01  qbf_prep_cycles:                        0
% 11.57/2.01  
% 11.57/2.01  ------ BMC1
% 11.57/2.01  
% 11.57/2.01  bmc1_current_bound:                     -1
% 11.57/2.01  bmc1_last_solved_bound:                 -1
% 11.57/2.01  bmc1_unsat_core_size:                   -1
% 11.57/2.01  bmc1_unsat_core_parents_size:           -1
% 11.57/2.01  bmc1_merge_next_fun:                    0
% 11.57/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.57/2.01  
% 11.57/2.01  ------ Instantiation
% 11.57/2.01  
% 11.57/2.01  inst_num_of_clauses:                    3973
% 11.57/2.01  inst_num_in_passive:                    967
% 11.57/2.01  inst_num_in_active:                     2386
% 11.57/2.01  inst_num_in_unprocessed:                620
% 11.57/2.01  inst_num_of_loops:                      2540
% 11.57/2.01  inst_num_of_learning_restarts:          0
% 11.57/2.01  inst_num_moves_active_passive:          146
% 11.57/2.01  inst_lit_activity:                      0
% 11.57/2.01  inst_lit_activity_moves:                0
% 11.57/2.01  inst_num_tautologies:                   0
% 11.57/2.01  inst_num_prop_implied:                  0
% 11.57/2.01  inst_num_existing_simplified:           0
% 11.57/2.01  inst_num_eq_res_simplified:             0
% 11.57/2.01  inst_num_child_elim:                    0
% 11.57/2.01  inst_num_of_dismatching_blockings:      2233
% 11.57/2.01  inst_num_of_non_proper_insts:           6834
% 11.57/2.01  inst_num_of_duplicates:                 0
% 11.57/2.01  inst_inst_num_from_inst_to_res:         0
% 11.57/2.01  inst_dismatching_checking_time:         0.
% 11.57/2.01  
% 11.57/2.01  ------ Resolution
% 11.57/2.01  
% 11.57/2.01  res_num_of_clauses:                     0
% 11.57/2.01  res_num_in_passive:                     0
% 11.57/2.01  res_num_in_active:                      0
% 11.57/2.01  res_num_of_loops:                       142
% 11.57/2.01  res_forward_subset_subsumed:            736
% 11.57/2.01  res_backward_subset_subsumed:           2
% 11.57/2.01  res_forward_subsumed:                   0
% 11.57/2.01  res_backward_subsumed:                  0
% 11.57/2.01  res_forward_subsumption_resolution:     0
% 11.57/2.01  res_backward_subsumption_resolution:    0
% 11.57/2.01  res_clause_to_clause_subsumption:       4085
% 11.57/2.01  res_orphan_elimination:                 0
% 11.57/2.01  res_tautology_del:                      777
% 11.57/2.01  res_num_eq_res_simplified:              0
% 11.57/2.01  res_num_sel_changes:                    0
% 11.57/2.01  res_moves_from_active_to_pass:          0
% 11.57/2.01  
% 11.57/2.01  ------ Superposition
% 11.57/2.01  
% 11.57/2.01  sup_time_total:                         0.
% 11.57/2.01  sup_time_generating:                    0.
% 11.57/2.01  sup_time_sim_full:                      0.
% 11.57/2.01  sup_time_sim_immed:                     0.
% 11.57/2.01  
% 11.57/2.01  sup_num_of_clauses:                     1964
% 11.57/2.01  sup_num_in_active:                      484
% 11.57/2.01  sup_num_in_passive:                     1480
% 11.57/2.01  sup_num_of_loops:                       506
% 11.57/2.01  sup_fw_superposition:                   1131
% 11.57/2.01  sup_bw_superposition:                   1034
% 11.57/2.01  sup_immediate_simplified:               566
% 11.57/2.01  sup_given_eliminated:                   1
% 11.57/2.01  comparisons_done:                       0
% 11.57/2.01  comparisons_avoided:                    3
% 11.57/2.01  
% 11.57/2.01  ------ Simplifications
% 11.57/2.01  
% 11.57/2.01  
% 11.57/2.01  sim_fw_subset_subsumed:                 6
% 11.57/2.01  sim_bw_subset_subsumed:                 80
% 11.57/2.01  sim_fw_subsumed:                        5
% 11.57/2.01  sim_bw_subsumed:                        0
% 11.57/2.01  sim_fw_subsumption_res:                 0
% 11.57/2.01  sim_bw_subsumption_res:                 0
% 11.57/2.01  sim_tautology_del:                      0
% 11.57/2.01  sim_eq_tautology_del:                   83
% 11.57/2.01  sim_eq_res_simp:                        0
% 11.57/2.01  sim_fw_demodulated:                     28
% 11.57/2.01  sim_bw_demodulated:                     12
% 11.57/2.01  sim_light_normalised:                   603
% 11.57/2.01  sim_joinable_taut:                      0
% 11.57/2.01  sim_joinable_simp:                      0
% 11.57/2.01  sim_ac_normalised:                      0
% 11.57/2.01  sim_smt_subsumption:                    0
% 11.57/2.01  
%------------------------------------------------------------------------------
