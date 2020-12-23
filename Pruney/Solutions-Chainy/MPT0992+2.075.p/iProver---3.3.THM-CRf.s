%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:02 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  222 (4363 expanded)
%              Number of clauses        :  152 (1529 expanded)
%              Number of leaves         :   17 ( 800 expanded)
%              Depth                    :   31
%              Number of atoms          :  668 (23356 expanded)
%              Number of equality atoms :  400 (6957 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37])).

fof(f66,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f36,plain,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1295,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_448,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_450,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_27])).

cnf(c_1294,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1300,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2514,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1294,c_1300])).

cnf(c_2539,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_450,c_2514])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1301,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3130,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_1301])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2250,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1304])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_201,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_202,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_202])).

cnf(c_1292,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_2326,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_1292])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1303,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2403,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2326,c_1303])).

cnf(c_3439,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3130,c_2403])).

cnf(c_3440,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3439])).

cnf(c_3451,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1295,c_3440])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1296,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4772,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1296])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1604,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3741,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_4956,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4772,c_29,c_27,c_3741])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1298,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5011,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4956,c_1298])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5181,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5011,c_30,c_32])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5191,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5181,c_1299])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1307,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6445,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5191,c_1300])).

cnf(c_9788,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3451,c_6445])).

cnf(c_9840,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1307,c_9788])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_432,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_1287,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_4963,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4956,c_1287])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2171,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1297])).

cnf(c_1583,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1759,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_1760,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_2329,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_30,c_32,c_1760])).

cnf(c_4964,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4956,c_2329])).

cnf(c_4971,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4963,c_4964])).

cnf(c_10350,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9840,c_4971])).

cnf(c_11208,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10350,c_3451])).

cnf(c_11216,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5191,c_11208])).

cnf(c_11230,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3451,c_11216])).

cnf(c_2461,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2464,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_11273,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11230,c_2464])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_400,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_1289,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1442,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1289,c_5])).

cnf(c_4960,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4956,c_1442])).

cnf(c_4998,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4960,c_4964])).

cnf(c_11295,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11273,c_4998])).

cnf(c_15,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_353,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_354,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1291,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1429,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1291,c_4])).

cnf(c_79,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_84,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_86,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_1879,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1429,c_81,c_86])).

cnf(c_1880,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1879])).

cnf(c_4961,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4956,c_1880])).

cnf(c_4988,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4961,c_4964])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1534,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_725,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1714,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_380,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1290,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1380,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1290,c_4])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_726,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1550,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1719,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_1720,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1799,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1800,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_2039,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1380,c_25,c_82,c_83,c_1719,c_1720,c_1800])).

cnf(c_2040,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2039])).

cnf(c_2064,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2065,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_727,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1667,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_2054,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_2466,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_4469,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6630,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4988,c_26,c_25,c_82,c_83,c_1534,c_1714,c_1800,c_2466,c_4469])).

cnf(c_6631,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6630])).

cnf(c_11296,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11273,c_6631])).

cnf(c_11413,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11296])).

cnf(c_11422,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11295,c_11413])).

cnf(c_11423,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11422])).

cnf(c_5190,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_5181,c_1300])).

cnf(c_11302,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_11273,c_5190])).

cnf(c_11324,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11273,c_25])).

cnf(c_11325,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11324])).

cnf(c_11388,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11302,c_11325])).

cnf(c_11424,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11423,c_11388])).

cnf(c_11306,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11273,c_5181])).

cnf(c_11379,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11306,c_11325])).

cnf(c_11381,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11379,c_5])).

cnf(c_11428,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11424,c_11381])).

cnf(c_1306,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3128,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_1301])).

cnf(c_7125,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2403,c_3128])).

cnf(c_11429,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11428,c_7125])).

cnf(c_11430,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11429])).

cnf(c_11431,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11430,c_5])).

cnf(c_6442,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_5191])).

cnf(c_8647,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7125,c_6442])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11431,c_8647,c_86])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options
% 3.61/0.99  
% 3.61/0.99  --out_options                           all
% 3.61/0.99  --tptp_safe_out                         true
% 3.61/0.99  --problem_path                          ""
% 3.61/0.99  --include_path                          ""
% 3.61/0.99  --clausifier                            res/vclausify_rel
% 3.61/0.99  --clausifier_options                    --mode clausify
% 3.61/0.99  --stdin                                 false
% 3.61/0.99  --stats_out                             all
% 3.61/0.99  
% 3.61/0.99  ------ General Options
% 3.61/0.99  
% 3.61/0.99  --fof                                   false
% 3.61/0.99  --time_out_real                         305.
% 3.61/0.99  --time_out_virtual                      -1.
% 3.61/0.99  --symbol_type_check                     false
% 3.61/0.99  --clausify_out                          false
% 3.61/0.99  --sig_cnt_out                           false
% 3.61/0.99  --trig_cnt_out                          false
% 3.61/0.99  --trig_cnt_out_tolerance                1.
% 3.61/0.99  --trig_cnt_out_sk_spl                   false
% 3.61/0.99  --abstr_cl_out                          false
% 3.61/0.99  
% 3.61/0.99  ------ Global Options
% 3.61/0.99  
% 3.61/0.99  --schedule                              default
% 3.61/0.99  --add_important_lit                     false
% 3.61/0.99  --prop_solver_per_cl                    1000
% 3.61/0.99  --min_unsat_core                        false
% 3.61/0.99  --soft_assumptions                      false
% 3.61/0.99  --soft_lemma_size                       3
% 3.61/0.99  --prop_impl_unit_size                   0
% 3.61/0.99  --prop_impl_unit                        []
% 3.61/0.99  --share_sel_clauses                     true
% 3.61/0.99  --reset_solvers                         false
% 3.61/0.99  --bc_imp_inh                            [conj_cone]
% 3.61/0.99  --conj_cone_tolerance                   3.
% 3.61/0.99  --extra_neg_conj                        none
% 3.61/0.99  --large_theory_mode                     true
% 3.61/0.99  --prolific_symb_bound                   200
% 3.61/0.99  --lt_threshold                          2000
% 3.61/0.99  --clause_weak_htbl                      true
% 3.61/0.99  --gc_record_bc_elim                     false
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing Options
% 3.61/0.99  
% 3.61/0.99  --preprocessing_flag                    true
% 3.61/0.99  --time_out_prep_mult                    0.1
% 3.61/0.99  --splitting_mode                        input
% 3.61/0.99  --splitting_grd                         true
% 3.61/0.99  --splitting_cvd                         false
% 3.61/0.99  --splitting_cvd_svl                     false
% 3.61/0.99  --splitting_nvd                         32
% 3.61/0.99  --sub_typing                            true
% 3.61/0.99  --prep_gs_sim                           true
% 3.61/0.99  --prep_unflatten                        true
% 3.61/0.99  --prep_res_sim                          true
% 3.61/0.99  --prep_upred                            true
% 3.61/0.99  --prep_sem_filter                       exhaustive
% 3.61/0.99  --prep_sem_filter_out                   false
% 3.61/0.99  --pred_elim                             true
% 3.61/0.99  --res_sim_input                         true
% 3.61/0.99  --eq_ax_congr_red                       true
% 3.61/0.99  --pure_diseq_elim                       true
% 3.61/0.99  --brand_transform                       false
% 3.61/0.99  --non_eq_to_eq                          false
% 3.61/0.99  --prep_def_merge                        true
% 3.61/0.99  --prep_def_merge_prop_impl              false
% 3.61/0.99  --prep_def_merge_mbd                    true
% 3.61/0.99  --prep_def_merge_tr_red                 false
% 3.61/0.99  --prep_def_merge_tr_cl                  false
% 3.61/0.99  --smt_preprocessing                     true
% 3.61/0.99  --smt_ac_axioms                         fast
% 3.61/0.99  --preprocessed_out                      false
% 3.61/0.99  --preprocessed_stats                    false
% 3.61/0.99  
% 3.61/0.99  ------ Abstraction refinement Options
% 3.61/0.99  
% 3.61/0.99  --abstr_ref                             []
% 3.61/0.99  --abstr_ref_prep                        false
% 3.61/0.99  --abstr_ref_until_sat                   false
% 3.61/0.99  --abstr_ref_sig_restrict                funpre
% 3.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.99  --abstr_ref_under                       []
% 3.61/0.99  
% 3.61/0.99  ------ SAT Options
% 3.61/0.99  
% 3.61/0.99  --sat_mode                              false
% 3.61/0.99  --sat_fm_restart_options                ""
% 3.61/0.99  --sat_gr_def                            false
% 3.61/0.99  --sat_epr_types                         true
% 3.61/0.99  --sat_non_cyclic_types                  false
% 3.61/0.99  --sat_finite_models                     false
% 3.61/0.99  --sat_fm_lemmas                         false
% 3.61/0.99  --sat_fm_prep                           false
% 3.61/0.99  --sat_fm_uc_incr                        true
% 3.61/0.99  --sat_out_model                         small
% 3.61/0.99  --sat_out_clauses                       false
% 3.61/0.99  
% 3.61/0.99  ------ QBF Options
% 3.61/0.99  
% 3.61/0.99  --qbf_mode                              false
% 3.61/0.99  --qbf_elim_univ                         false
% 3.61/0.99  --qbf_dom_inst                          none
% 3.61/0.99  --qbf_dom_pre_inst                      false
% 3.61/0.99  --qbf_sk_in                             false
% 3.61/0.99  --qbf_pred_elim                         true
% 3.61/0.99  --qbf_split                             512
% 3.61/0.99  
% 3.61/0.99  ------ BMC1 Options
% 3.61/0.99  
% 3.61/0.99  --bmc1_incremental                      false
% 3.61/0.99  --bmc1_axioms                           reachable_all
% 3.61/0.99  --bmc1_min_bound                        0
% 3.61/0.99  --bmc1_max_bound                        -1
% 3.61/0.99  --bmc1_max_bound_default                -1
% 3.61/0.99  --bmc1_symbol_reachability              true
% 3.61/0.99  --bmc1_property_lemmas                  false
% 3.61/0.99  --bmc1_k_induction                      false
% 3.61/0.99  --bmc1_non_equiv_states                 false
% 3.61/0.99  --bmc1_deadlock                         false
% 3.61/0.99  --bmc1_ucm                              false
% 3.61/0.99  --bmc1_add_unsat_core                   none
% 3.61/0.99  --bmc1_unsat_core_children              false
% 3.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.99  --bmc1_out_stat                         full
% 3.61/0.99  --bmc1_ground_init                      false
% 3.61/0.99  --bmc1_pre_inst_next_state              false
% 3.61/0.99  --bmc1_pre_inst_state                   false
% 3.61/0.99  --bmc1_pre_inst_reach_state             false
% 3.61/0.99  --bmc1_out_unsat_core                   false
% 3.61/0.99  --bmc1_aig_witness_out                  false
% 3.61/0.99  --bmc1_verbose                          false
% 3.61/0.99  --bmc1_dump_clauses_tptp                false
% 3.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.99  --bmc1_dump_file                        -
% 3.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.99  --bmc1_ucm_extend_mode                  1
% 3.61/0.99  --bmc1_ucm_init_mode                    2
% 3.61/0.99  --bmc1_ucm_cone_mode                    none
% 3.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.99  --bmc1_ucm_relax_model                  4
% 3.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.99  --bmc1_ucm_layered_model                none
% 3.61/0.99  --bmc1_ucm_max_lemma_size               10
% 3.61/0.99  
% 3.61/0.99  ------ AIG Options
% 3.61/0.99  
% 3.61/0.99  --aig_mode                              false
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation Options
% 3.61/0.99  
% 3.61/0.99  --instantiation_flag                    true
% 3.61/0.99  --inst_sos_flag                         false
% 3.61/0.99  --inst_sos_phase                        true
% 3.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel_side                     num_symb
% 3.61/0.99  --inst_solver_per_active                1400
% 3.61/0.99  --inst_solver_calls_frac                1.
% 3.61/0.99  --inst_passive_queue_type               priority_queues
% 3.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.99  --inst_passive_queues_freq              [25;2]
% 3.61/0.99  --inst_dismatching                      true
% 3.61/0.99  --inst_eager_unprocessed_to_passive     true
% 3.61/0.99  --inst_prop_sim_given                   true
% 3.61/0.99  --inst_prop_sim_new                     false
% 3.61/0.99  --inst_subs_new                         false
% 3.61/0.99  --inst_eq_res_simp                      false
% 3.61/0.99  --inst_subs_given                       false
% 3.61/0.99  --inst_orphan_elimination               true
% 3.61/0.99  --inst_learning_loop_flag               true
% 3.61/0.99  --inst_learning_start                   3000
% 3.61/0.99  --inst_learning_factor                  2
% 3.61/0.99  --inst_start_prop_sim_after_learn       3
% 3.61/0.99  --inst_sel_renew                        solver
% 3.61/0.99  --inst_lit_activity_flag                true
% 3.61/0.99  --inst_restr_to_given                   false
% 3.61/0.99  --inst_activity_threshold               500
% 3.61/0.99  --inst_out_proof                        true
% 3.61/0.99  
% 3.61/0.99  ------ Resolution Options
% 3.61/0.99  
% 3.61/0.99  --resolution_flag                       true
% 3.61/0.99  --res_lit_sel                           adaptive
% 3.61/0.99  --res_lit_sel_side                      none
% 3.61/0.99  --res_ordering                          kbo
% 3.61/0.99  --res_to_prop_solver                    active
% 3.61/0.99  --res_prop_simpl_new                    false
% 3.61/0.99  --res_prop_simpl_given                  true
% 3.61/0.99  --res_passive_queue_type                priority_queues
% 3.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.99  --res_passive_queues_freq               [15;5]
% 3.61/0.99  --res_forward_subs                      full
% 3.61/0.99  --res_backward_subs                     full
% 3.61/0.99  --res_forward_subs_resolution           true
% 3.61/0.99  --res_backward_subs_resolution          true
% 3.61/0.99  --res_orphan_elimination                true
% 3.61/0.99  --res_time_limit                        2.
% 3.61/0.99  --res_out_proof                         true
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Options
% 3.61/0.99  
% 3.61/0.99  --superposition_flag                    true
% 3.61/0.99  --sup_passive_queue_type                priority_queues
% 3.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.99  --demod_completeness_check              fast
% 3.61/0.99  --demod_use_ground                      true
% 3.61/0.99  --sup_to_prop_solver                    passive
% 3.61/0.99  --sup_prop_simpl_new                    true
% 3.61/0.99  --sup_prop_simpl_given                  true
% 3.61/0.99  --sup_fun_splitting                     false
% 3.61/0.99  --sup_smt_interval                      50000
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Simplification Setup
% 3.61/0.99  
% 3.61/0.99  --sup_indices_passive                   []
% 3.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_full_bw                           [BwDemod]
% 3.61/0.99  --sup_immed_triv                        [TrivRules]
% 3.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_immed_bw_main                     []
% 3.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  
% 3.61/0.99  ------ Combination Options
% 3.61/0.99  
% 3.61/0.99  --comb_res_mult                         3
% 3.61/0.99  --comb_sup_mult                         2
% 3.61/0.99  --comb_inst_mult                        10
% 3.61/0.99  
% 3.61/0.99  ------ Debug Options
% 3.61/0.99  
% 3.61/0.99  --dbg_backtrace                         false
% 3.61/0.99  --dbg_dump_prop_clauses                 false
% 3.61/0.99  --dbg_dump_prop_clauses_file            -
% 3.61/0.99  --dbg_out_stat                          false
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 28
% 3.61/0.99  conjectures                             4
% 3.61/0.99  EPR                                     7
% 3.61/0.99  Horn                                    25
% 3.61/0.99  unary                                   8
% 3.61/0.99  binary                                  6
% 3.61/0.99  lits                                    70
% 3.61/0.99  lits eq                                 27
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 1
% 3.61/0.99  fd_pseudo_cond                          1
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Schedule dynamic 5 is on 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options
% 3.61/0.99  
% 3.61/0.99  --out_options                           all
% 3.61/0.99  --tptp_safe_out                         true
% 3.61/0.99  --problem_path                          ""
% 3.61/0.99  --include_path                          ""
% 3.61/0.99  --clausifier                            res/vclausify_rel
% 3.61/0.99  --clausifier_options                    --mode clausify
% 3.61/0.99  --stdin                                 false
% 3.61/0.99  --stats_out                             all
% 3.61/0.99  
% 3.61/0.99  ------ General Options
% 3.61/0.99  
% 3.61/0.99  --fof                                   false
% 3.61/0.99  --time_out_real                         305.
% 3.61/0.99  --time_out_virtual                      -1.
% 3.61/0.99  --symbol_type_check                     false
% 3.61/0.99  --clausify_out                          false
% 3.61/0.99  --sig_cnt_out                           false
% 3.61/0.99  --trig_cnt_out                          false
% 3.61/0.99  --trig_cnt_out_tolerance                1.
% 3.61/0.99  --trig_cnt_out_sk_spl                   false
% 3.61/0.99  --abstr_cl_out                          false
% 3.61/0.99  
% 3.61/0.99  ------ Global Options
% 3.61/0.99  
% 3.61/0.99  --schedule                              default
% 3.61/0.99  --add_important_lit                     false
% 3.61/0.99  --prop_solver_per_cl                    1000
% 3.61/0.99  --min_unsat_core                        false
% 3.61/0.99  --soft_assumptions                      false
% 3.61/0.99  --soft_lemma_size                       3
% 3.61/0.99  --prop_impl_unit_size                   0
% 3.61/0.99  --prop_impl_unit                        []
% 3.61/0.99  --share_sel_clauses                     true
% 3.61/0.99  --reset_solvers                         false
% 3.61/0.99  --bc_imp_inh                            [conj_cone]
% 3.61/0.99  --conj_cone_tolerance                   3.
% 3.61/0.99  --extra_neg_conj                        none
% 3.61/0.99  --large_theory_mode                     true
% 3.61/0.99  --prolific_symb_bound                   200
% 3.61/0.99  --lt_threshold                          2000
% 3.61/0.99  --clause_weak_htbl                      true
% 3.61/0.99  --gc_record_bc_elim                     false
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing Options
% 3.61/0.99  
% 3.61/0.99  --preprocessing_flag                    true
% 3.61/0.99  --time_out_prep_mult                    0.1
% 3.61/0.99  --splitting_mode                        input
% 3.61/0.99  --splitting_grd                         true
% 3.61/0.99  --splitting_cvd                         false
% 3.61/0.99  --splitting_cvd_svl                     false
% 3.61/0.99  --splitting_nvd                         32
% 3.61/0.99  --sub_typing                            true
% 3.61/0.99  --prep_gs_sim                           true
% 3.61/0.99  --prep_unflatten                        true
% 3.61/0.99  --prep_res_sim                          true
% 3.61/0.99  --prep_upred                            true
% 3.61/0.99  --prep_sem_filter                       exhaustive
% 3.61/0.99  --prep_sem_filter_out                   false
% 3.61/0.99  --pred_elim                             true
% 3.61/0.99  --res_sim_input                         true
% 3.61/0.99  --eq_ax_congr_red                       true
% 3.61/0.99  --pure_diseq_elim                       true
% 3.61/0.99  --brand_transform                       false
% 3.61/0.99  --non_eq_to_eq                          false
% 3.61/0.99  --prep_def_merge                        true
% 3.61/0.99  --prep_def_merge_prop_impl              false
% 3.61/0.99  --prep_def_merge_mbd                    true
% 3.61/0.99  --prep_def_merge_tr_red                 false
% 3.61/0.99  --prep_def_merge_tr_cl                  false
% 3.61/0.99  --smt_preprocessing                     true
% 3.61/0.99  --smt_ac_axioms                         fast
% 3.61/0.99  --preprocessed_out                      false
% 3.61/0.99  --preprocessed_stats                    false
% 3.61/0.99  
% 3.61/0.99  ------ Abstraction refinement Options
% 3.61/0.99  
% 3.61/0.99  --abstr_ref                             []
% 3.61/0.99  --abstr_ref_prep                        false
% 3.61/0.99  --abstr_ref_until_sat                   false
% 3.61/0.99  --abstr_ref_sig_restrict                funpre
% 3.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.99  --abstr_ref_under                       []
% 3.61/0.99  
% 3.61/0.99  ------ SAT Options
% 3.61/0.99  
% 3.61/0.99  --sat_mode                              false
% 3.61/0.99  --sat_fm_restart_options                ""
% 3.61/0.99  --sat_gr_def                            false
% 3.61/0.99  --sat_epr_types                         true
% 3.61/0.99  --sat_non_cyclic_types                  false
% 3.61/0.99  --sat_finite_models                     false
% 3.61/0.99  --sat_fm_lemmas                         false
% 3.61/0.99  --sat_fm_prep                           false
% 3.61/0.99  --sat_fm_uc_incr                        true
% 3.61/0.99  --sat_out_model                         small
% 3.61/0.99  --sat_out_clauses                       false
% 3.61/0.99  
% 3.61/0.99  ------ QBF Options
% 3.61/0.99  
% 3.61/0.99  --qbf_mode                              false
% 3.61/0.99  --qbf_elim_univ                         false
% 3.61/0.99  --qbf_dom_inst                          none
% 3.61/0.99  --qbf_dom_pre_inst                      false
% 3.61/0.99  --qbf_sk_in                             false
% 3.61/0.99  --qbf_pred_elim                         true
% 3.61/0.99  --qbf_split                             512
% 3.61/0.99  
% 3.61/0.99  ------ BMC1 Options
% 3.61/0.99  
% 3.61/0.99  --bmc1_incremental                      false
% 3.61/0.99  --bmc1_axioms                           reachable_all
% 3.61/0.99  --bmc1_min_bound                        0
% 3.61/0.99  --bmc1_max_bound                        -1
% 3.61/0.99  --bmc1_max_bound_default                -1
% 3.61/0.99  --bmc1_symbol_reachability              true
% 3.61/0.99  --bmc1_property_lemmas                  false
% 3.61/0.99  --bmc1_k_induction                      false
% 3.61/0.99  --bmc1_non_equiv_states                 false
% 3.61/0.99  --bmc1_deadlock                         false
% 3.61/0.99  --bmc1_ucm                              false
% 3.61/0.99  --bmc1_add_unsat_core                   none
% 3.61/0.99  --bmc1_unsat_core_children              false
% 3.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.99  --bmc1_out_stat                         full
% 3.61/0.99  --bmc1_ground_init                      false
% 3.61/0.99  --bmc1_pre_inst_next_state              false
% 3.61/0.99  --bmc1_pre_inst_state                   false
% 3.61/0.99  --bmc1_pre_inst_reach_state             false
% 3.61/0.99  --bmc1_out_unsat_core                   false
% 3.61/0.99  --bmc1_aig_witness_out                  false
% 3.61/0.99  --bmc1_verbose                          false
% 3.61/0.99  --bmc1_dump_clauses_tptp                false
% 3.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.99  --bmc1_dump_file                        -
% 3.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.99  --bmc1_ucm_extend_mode                  1
% 3.61/0.99  --bmc1_ucm_init_mode                    2
% 3.61/0.99  --bmc1_ucm_cone_mode                    none
% 3.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.99  --bmc1_ucm_relax_model                  4
% 3.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.99  --bmc1_ucm_layered_model                none
% 3.61/0.99  --bmc1_ucm_max_lemma_size               10
% 3.61/0.99  
% 3.61/0.99  ------ AIG Options
% 3.61/0.99  
% 3.61/0.99  --aig_mode                              false
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation Options
% 3.61/0.99  
% 3.61/0.99  --instantiation_flag                    true
% 3.61/0.99  --inst_sos_flag                         false
% 3.61/0.99  --inst_sos_phase                        true
% 3.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel_side                     none
% 3.61/0.99  --inst_solver_per_active                1400
% 3.61/0.99  --inst_solver_calls_frac                1.
% 3.61/0.99  --inst_passive_queue_type               priority_queues
% 3.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.99  --inst_passive_queues_freq              [25;2]
% 3.61/0.99  --inst_dismatching                      true
% 3.61/0.99  --inst_eager_unprocessed_to_passive     true
% 3.61/0.99  --inst_prop_sim_given                   true
% 3.61/0.99  --inst_prop_sim_new                     false
% 3.61/0.99  --inst_subs_new                         false
% 3.61/0.99  --inst_eq_res_simp                      false
% 3.61/0.99  --inst_subs_given                       false
% 3.61/0.99  --inst_orphan_elimination               true
% 3.61/0.99  --inst_learning_loop_flag               true
% 3.61/0.99  --inst_learning_start                   3000
% 3.61/0.99  --inst_learning_factor                  2
% 3.61/0.99  --inst_start_prop_sim_after_learn       3
% 3.61/0.99  --inst_sel_renew                        solver
% 3.61/0.99  --inst_lit_activity_flag                true
% 3.61/0.99  --inst_restr_to_given                   false
% 3.61/0.99  --inst_activity_threshold               500
% 3.61/0.99  --inst_out_proof                        true
% 3.61/0.99  
% 3.61/0.99  ------ Resolution Options
% 3.61/0.99  
% 3.61/0.99  --resolution_flag                       false
% 3.61/0.99  --res_lit_sel                           adaptive
% 3.61/0.99  --res_lit_sel_side                      none
% 3.61/0.99  --res_ordering                          kbo
% 3.61/0.99  --res_to_prop_solver                    active
% 3.61/0.99  --res_prop_simpl_new                    false
% 3.61/0.99  --res_prop_simpl_given                  true
% 3.61/0.99  --res_passive_queue_type                priority_queues
% 3.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.99  --res_passive_queues_freq               [15;5]
% 3.61/0.99  --res_forward_subs                      full
% 3.61/0.99  --res_backward_subs                     full
% 3.61/0.99  --res_forward_subs_resolution           true
% 3.61/0.99  --res_backward_subs_resolution          true
% 3.61/0.99  --res_orphan_elimination                true
% 3.61/0.99  --res_time_limit                        2.
% 3.61/0.99  --res_out_proof                         true
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Options
% 3.61/0.99  
% 3.61/0.99  --superposition_flag                    true
% 3.61/0.99  --sup_passive_queue_type                priority_queues
% 3.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.99  --demod_completeness_check              fast
% 3.61/0.99  --demod_use_ground                      true
% 3.61/0.99  --sup_to_prop_solver                    passive
% 3.61/0.99  --sup_prop_simpl_new                    true
% 3.61/0.99  --sup_prop_simpl_given                  true
% 3.61/0.99  --sup_fun_splitting                     false
% 3.61/0.99  --sup_smt_interval                      50000
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Simplification Setup
% 3.61/0.99  
% 3.61/0.99  --sup_indices_passive                   []
% 3.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_full_bw                           [BwDemod]
% 3.61/0.99  --sup_immed_triv                        [TrivRules]
% 3.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_immed_bw_main                     []
% 3.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  
% 3.61/0.99  ------ Combination Options
% 3.61/0.99  
% 3.61/0.99  --comb_res_mult                         3
% 3.61/0.99  --comb_sup_mult                         2
% 3.61/0.99  --comb_inst_mult                        10
% 3.61/0.99  
% 3.61/0.99  ------ Debug Options
% 3.61/0.99  
% 3.61/0.99  --dbg_backtrace                         false
% 3.61/0.99  --dbg_dump_prop_clauses                 false
% 3.61/0.99  --dbg_dump_prop_clauses_file            -
% 3.61/0.99  --dbg_out_stat                          false
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f14,conjecture,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f15,negated_conjecture,(
% 3.61/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.61/0.99    inference(negated_conjecture,[],[f14])).
% 3.61/0.99  
% 3.61/0.99  fof(f29,plain,(
% 3.61/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.61/0.99    inference(ennf_transformation,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.61/0.99    inference(flattening,[],[f29])).
% 3.61/0.99  
% 3.61/0.99  fof(f37,plain,(
% 3.61/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f66,plain,(
% 3.61/0.99    r1_tarski(sK2,sK0)),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f11,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(ennf_transformation,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(flattening,[],[f23])).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(nnf_transformation,[],[f24])).
% 3.61/0.99  
% 3.61/0.99  fof(f54,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f64,plain,(
% 3.61/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f65,plain,(
% 3.61/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f9,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f20,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(ennf_transformation,[],[f9])).
% 3.61/0.99  
% 3.61/0.99  fof(f52,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f20])).
% 3.61/0.99  
% 3.61/0.99  fof(f8,axiom,(
% 3.61/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f18,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f8])).
% 3.61/0.99  
% 3.61/0.99  fof(f19,plain,(
% 3.61/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(flattening,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f51,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f19])).
% 3.61/0.99  
% 3.61/0.99  fof(f4,axiom,(
% 3.61/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.99    inference(nnf_transformation,[],[f4])).
% 3.61/0.99  
% 3.61/0.99  fof(f46,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f5,axiom,(
% 3.61/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f16,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f5])).
% 3.61/0.99  
% 3.61/0.99  fof(f48,plain,(
% 3.61/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f16])).
% 3.61/0.99  
% 3.61/0.99  fof(f47,plain,(
% 3.61/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f6,axiom,(
% 3.61/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f49,plain,(
% 3.61/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f6])).
% 3.61/0.99  
% 3.61/0.99  fof(f13,axiom,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f27,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.61/0.99    inference(ennf_transformation,[],[f13])).
% 3.61/0.99  
% 3.61/0.99  fof(f28,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.61/0.99    inference(flattening,[],[f27])).
% 3.61/0.99  
% 3.61/0.99  fof(f62,plain,(
% 3.61/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f28])).
% 3.61/0.99  
% 3.61/0.99  fof(f63,plain,(
% 3.61/0.99    v1_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f12,axiom,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f25,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.61/0.99    inference(ennf_transformation,[],[f12])).
% 3.61/0.99  
% 3.61/0.99  fof(f26,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.61/0.99    inference(flattening,[],[f25])).
% 3.61/0.99  
% 3.61/0.99  fof(f61,plain,(
% 3.61/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f26])).
% 3.61/0.99  
% 3.61/0.99  fof(f10,axiom,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.61/0.99    inference(ennf_transformation,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.61/0.99    inference(flattening,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  fof(f53,plain,(
% 3.61/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f31,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(nnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f32,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(flattening,[],[f31])).
% 3.61/0.99  
% 3.61/0.99  fof(f39,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.61/0.99    inference(cnf_transformation,[],[f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f70,plain,(
% 3.61/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.61/0.99    inference(equality_resolution,[],[f39])).
% 3.61/0.99  
% 3.61/0.99  fof(f56,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f68,plain,(
% 3.61/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f60,plain,(
% 3.61/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f26])).
% 3.61/0.99  
% 3.61/0.99  fof(f57,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f76,plain,(
% 3.61/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.61/0.99    inference(equality_resolution,[],[f57])).
% 3.61/0.99  
% 3.61/0.99  fof(f3,axiom,(
% 3.61/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f33,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.61/0.99    inference(nnf_transformation,[],[f3])).
% 3.61/0.99  
% 3.61/0.99  fof(f34,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.61/0.99    inference(flattening,[],[f33])).
% 3.61/0.99  
% 3.61/0.99  fof(f44,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f34])).
% 3.61/0.99  
% 3.61/0.99  fof(f72,plain,(
% 3.61/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.61/0.99    inference(equality_resolution,[],[f44])).
% 3.61/0.99  
% 3.61/0.99  fof(f59,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f73,plain,(
% 3.61/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(equality_resolution,[],[f59])).
% 3.61/0.99  
% 3.61/0.99  fof(f74,plain,(
% 3.61/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.61/0.99    inference(equality_resolution,[],[f73])).
% 3.61/0.99  
% 3.61/0.99  fof(f45,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.61/0.99    inference(cnf_transformation,[],[f34])).
% 3.61/0.99  
% 3.61/0.99  fof(f71,plain,(
% 3.61/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.61/0.99    inference(equality_resolution,[],[f45])).
% 3.61/0.99  
% 3.61/0.99  fof(f2,axiom,(
% 3.61/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f42,plain,(
% 3.61/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f2])).
% 3.61/0.99  
% 3.61/0.99  fof(f43,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f34])).
% 3.61/0.99  
% 3.61/0.99  fof(f41,plain,(
% 3.61/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f58,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f75,plain,(
% 3.61/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.61/0.99    inference(equality_resolution,[],[f58])).
% 3.61/0.99  
% 3.61/0.99  fof(f67,plain,(
% 3.61/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.61/0.99    inference(cnf_transformation,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_26,negated_conjecture,
% 3.61/0.99      ( r1_tarski(sK2,sK0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1295,plain,
% 3.61/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_20,plain,
% 3.61/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_28,negated_conjecture,
% 3.61/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_447,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.61/0.99      | sK3 != X0
% 3.61/0.99      | sK1 != X2
% 3.61/0.99      | sK0 != X1
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_448,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.61/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.61/0.99      | k1_xboole_0 = sK1 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_27,negated_conjecture,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_450,plain,
% 3.61/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_448,c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1294,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1300,plain,
% 3.61/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2514,plain,
% 3.61/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1294,c_1300]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2539,plain,
% 3.61/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_450,c_2514]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1301,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.61/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.61/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3130,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2539,c_1301]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1304,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2250,plain,
% 3.61/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1294,c_1304]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | v1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_201,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.61/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_202,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_201]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_256,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.61/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_202]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1292,plain,
% 3.61/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | v1_relat_1(X1) != iProver_top
% 3.61/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2326,plain,
% 3.61/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.61/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2250,c_1292]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1303,plain,
% 3.61/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2403,plain,
% 3.61/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_2326,c_1303]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3439,plain,
% 3.61/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3130,c_2403]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3440,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_3439]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3451,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1295,c_3440]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_23,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1296,plain,
% 3.61/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.61/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.61/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4772,plain,
% 3.61/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1294,c_1296]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_29,negated_conjecture,
% 3.61/0.99      ( v1_funct_1(sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1604,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/0.99      | ~ v1_funct_1(sK3)
% 3.61/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3741,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.61/0.99      | ~ v1_funct_1(sK3)
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1604]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4956,plain,
% 3.61/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4772,c_29,c_27,c_3741]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_21,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ v1_funct_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1298,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.61/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5011,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.61/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4956,c_1298]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_30,plain,
% 3.61/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_32,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5181,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_5011,c_30,c_32]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.61/0.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1299,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.61/0.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5191,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.61/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5181,c_1299]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1307,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6445,plain,
% 3.61/0.99      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 3.61/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5191,c_1300]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9788,plain,
% 3.61/0.99      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3451,c_6445]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9840,plain,
% 3.61/0.99      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.61/0.99      | sK1 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1307,c_9788]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18,plain,
% 3.61/0.99      ( v1_funct_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_24,negated_conjecture,
% 3.61/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.61/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_431,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.61/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.61/0.99      | sK2 != X1
% 3.61/0.99      | sK1 != X2
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_432,plain,
% 3.61/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.61/0.99      | k1_xboole_0 = sK1 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1287,plain,
% 3.61/0.99      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.61/0.99      | k1_xboole_0 = sK1
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4963,plain,
% 3.61/0.99      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4956,c_1287]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_22,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1297,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.99      | v1_funct_1(X0) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2171,plain,
% 3.61/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1294,c_1297]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1583,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.61/0.99      | ~ v1_funct_1(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1759,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.61/0.99      | ~ v1_funct_1(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1583]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1760,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2329,plain,
% 3.61/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_2171,c_30,c_32,c_1760]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4964,plain,
% 3.61/0.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4956,c_2329]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4971,plain,
% 3.61/0.99      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4963,c_4964]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10350,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.61/0.99      | sK1 = k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9840,c_4971]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11208,plain,
% 3.61/0.99      ( sK1 = k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_10350,c_3451]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11216,plain,
% 3.61/0.99      ( sK1 = k1_xboole_0
% 3.61/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5191,c_11208]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11230,plain,
% 3.61/0.99      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3451,c_11216]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2461,plain,
% 3.61/0.99      ( r1_tarski(sK2,sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2464,plain,
% 3.61/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2461]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11273,plain,
% 3.61/0.99      ( sK1 = k1_xboole_0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_11230,c_2464]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17,plain,
% 3.61/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.61/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_399,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.61/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.61/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | sK1 != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_400,plain,
% 3.61/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1289,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5,plain,
% 3.61/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1442,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1289,c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4960,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4956,c_1442]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4998,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4960,c_4964]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11295,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.61/0.99      | sK2 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11273,c_4998]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,plain,
% 3.61/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.61/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.61/0.99      | k1_xboole_0 = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_353,plain,
% 3.61/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK2 != X0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_354,plain,
% 3.61/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.61/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.61/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK2 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1291,plain,
% 3.61/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK2
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4,plain,
% 3.61/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1429,plain,
% 3.61/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1291,c_4]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_79,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_81,plain,
% 3.61/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_79]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_84,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_86,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1879,plain,
% 3.61/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1429,c_81,c_86]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1880,plain,
% 3.61/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_1879]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4961,plain,
% 3.61/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.61/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4956,c_1880]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4988,plain,
% 3.61/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4961,c_4964]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = X1
% 3.61/0.99      | k1_xboole_0 = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_82,plain,
% 3.61/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_83,plain,
% 3.61/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_0,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1534,plain,
% 3.61/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.61/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.61/0.99      | sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_725,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1714,plain,
% 3.61/0.99      ( sK2 = sK2 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_16,plain,
% 3.61/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.99      | k1_xboole_0 = X1
% 3.61/0.99      | k1_xboole_0 = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_379,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.99      | sK3 != X0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | sK0 != X1
% 3.61/0.99      | k1_xboole_0 = X1
% 3.61/0.99      | k1_xboole_0 = X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_380,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK3
% 3.61/0.99      | k1_xboole_0 = sK0 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_379]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1290,plain,
% 3.61/0.99      ( sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK3
% 3.61/0.99      | k1_xboole_0 = sK0
% 3.61/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1380,plain,
% 3.61/0.99      ( sK3 = k1_xboole_0
% 3.61/0.99      | sK1 != k1_xboole_0
% 3.61/0.99      | sK0 = k1_xboole_0
% 3.61/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1290,c_4]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_25,negated_conjecture,
% 3.61/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_726,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1550,plain,
% 3.61/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1719,plain,
% 3.61/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1550]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1720,plain,
% 3.61/0.99      ( sK0 = sK0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1799,plain,
% 3.61/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1800,plain,
% 3.61/0.99      ( sK1 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK1
% 3.61/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1799]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2039,plain,
% 3.61/0.99      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1380,c_25,c_82,c_83,c_1719,c_1720,c_1800]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2040,plain,
% 3.61/0.99      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_2039]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2064,plain,
% 3.61/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2065,plain,
% 3.61/0.99      ( sK0 != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 = sK0
% 3.61/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2064]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_727,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/0.99      theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1667,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1)
% 3.61/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.61/0.99      | sK2 != X0
% 3.61/0.99      | k1_xboole_0 != X1 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_727]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2054,plain,
% 3.61/0.99      ( ~ r1_tarski(sK2,X0)
% 3.61/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.61/0.99      | sK2 != sK2
% 3.61/0.99      | k1_xboole_0 != X0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1667]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2466,plain,
% 3.61/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.61/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.61/0.99      | sK2 != sK2
% 3.61/0.99      | k1_xboole_0 != sK0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2054]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4469,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6630,plain,
% 3.61/0.99      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4988,c_26,c_25,c_82,c_83,c_1534,c_1714,c_1800,c_2466,
% 3.61/0.99                 c_4469]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6631,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6630]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11296,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11273,c_6631]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11413,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(equality_resolution_simp,[status(thm)],[c_11296]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11422,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.61/0.99      | k1_xboole_0 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_11295,c_11413]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11423,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(equality_resolution_simp,[status(thm)],[c_11422]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5190,plain,
% 3.61/0.99      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5181,c_1300]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11302,plain,
% 3.61/0.99      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11273,c_5190]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11324,plain,
% 3.61/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11273,c_25]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11325,plain,
% 3.61/0.99      ( sK0 = k1_xboole_0 ),
% 3.61/0.99      inference(equality_resolution_simp,[status(thm)],[c_11324]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11388,plain,
% 3.61/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_11302,c_11325]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11424,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11423,c_11388]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11306,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11273,c_5181]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11379,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_11306,c_11325]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11381,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11379,c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11428,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_11424,c_11381]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1306,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3128,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.61/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1306,c_1301]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7125,plain,
% 3.61/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2403,c_3128]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11429,plain,
% 3.61/0.99      ( k1_xboole_0 != k1_xboole_0
% 3.61/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_11428,c_7125]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11430,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.61/0.99      inference(equality_resolution_simp,[status(thm)],[c_11429]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11431,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11430,c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6442,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5,c_5191]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8647,plain,
% 3.61/0.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_7125,c_6442]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,[status(thm)],[c_11431,c_8647,c_86]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ General
% 3.61/0.99  
% 3.61/0.99  abstr_ref_over_cycles:                  0
% 3.61/0.99  abstr_ref_under_cycles:                 0
% 3.61/0.99  gc_basic_clause_elim:                   0
% 3.61/0.99  forced_gc_time:                         0
% 3.61/0.99  parsing_time:                           0.009
% 3.61/0.99  unif_index_cands_time:                  0.
% 3.61/0.99  unif_index_add_time:                    0.
% 3.61/0.99  orderings_time:                         0.
% 3.61/0.99  out_proof_time:                         0.012
% 3.61/0.99  total_time:                             0.323
% 3.61/0.99  num_of_symbols:                         47
% 3.61/0.99  num_of_terms:                           11110
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing
% 3.61/0.99  
% 3.61/0.99  num_of_splits:                          0
% 3.61/0.99  num_of_split_atoms:                     0
% 3.61/0.99  num_of_reused_defs:                     0
% 3.61/0.99  num_eq_ax_congr_red:                    8
% 3.61/0.99  num_of_sem_filtered_clauses:            1
% 3.61/0.99  num_of_subtypes:                        0
% 3.61/0.99  monotx_restored_types:                  0
% 3.61/0.99  sat_num_of_epr_types:                   0
% 3.61/0.99  sat_num_of_non_cyclic_types:            0
% 3.61/0.99  sat_guarded_non_collapsed_types:        0
% 3.61/0.99  num_pure_diseq_elim:                    0
% 3.61/0.99  simp_replaced_by:                       0
% 3.61/0.99  res_preprocessed:                       136
% 3.61/0.99  prep_upred:                             0
% 3.61/0.99  prep_unflattend:                        33
% 3.61/0.99  smt_new_axioms:                         0
% 3.61/0.99  pred_elim_cands:                        4
% 3.61/0.99  pred_elim:                              1
% 3.61/0.99  pred_elim_cl:                           1
% 3.61/0.99  pred_elim_cycles:                       3
% 3.61/0.99  merged_defs:                            8
% 3.61/0.99  merged_defs_ncl:                        0
% 3.61/0.99  bin_hyper_res:                          9
% 3.61/0.99  prep_cycles:                            4
% 3.61/0.99  pred_elim_time:                         0.005
% 3.61/0.99  splitting_time:                         0.
% 3.61/0.99  sem_filter_time:                        0.
% 3.61/0.99  monotx_time:                            0.
% 3.61/0.99  subtype_inf_time:                       0.
% 3.61/0.99  
% 3.61/0.99  ------ Problem properties
% 3.61/0.99  
% 3.61/0.99  clauses:                                28
% 3.61/0.99  conjectures:                            4
% 3.61/0.99  epr:                                    7
% 3.61/0.99  horn:                                   25
% 3.61/0.99  ground:                                 11
% 3.61/0.99  unary:                                  8
% 3.61/0.99  binary:                                 6
% 3.61/0.99  lits:                                   70
% 3.61/0.99  lits_eq:                                27
% 3.61/0.99  fd_pure:                                0
% 3.61/0.99  fd_pseudo:                              0
% 3.61/0.99  fd_cond:                                1
% 3.61/0.99  fd_pseudo_cond:                         1
% 3.61/0.99  ac_symbols:                             0
% 3.61/0.99  
% 3.61/0.99  ------ Propositional Solver
% 3.61/0.99  
% 3.61/0.99  prop_solver_calls:                      29
% 3.61/0.99  prop_fast_solver_calls:                 1111
% 3.61/0.99  smt_solver_calls:                       0
% 3.61/0.99  smt_fast_solver_calls:                  0
% 3.61/0.99  prop_num_of_clauses:                    4546
% 3.61/0.99  prop_preprocess_simplified:             11880
% 3.61/0.99  prop_fo_subsumed:                       25
% 3.61/0.99  prop_solver_time:                       0.
% 3.61/0.99  smt_solver_time:                        0.
% 3.61/0.99  smt_fast_solver_time:                   0.
% 3.61/0.99  prop_fast_solver_time:                  0.
% 3.61/0.99  prop_unsat_core_time:                   0.
% 3.61/0.99  
% 3.61/0.99  ------ QBF
% 3.61/0.99  
% 3.61/0.99  qbf_q_res:                              0
% 3.61/0.99  qbf_num_tautologies:                    0
% 3.61/0.99  qbf_prep_cycles:                        0
% 3.61/0.99  
% 3.61/0.99  ------ BMC1
% 3.61/0.99  
% 3.61/0.99  bmc1_current_bound:                     -1
% 3.61/0.99  bmc1_last_solved_bound:                 -1
% 3.61/0.99  bmc1_unsat_core_size:                   -1
% 3.61/0.99  bmc1_unsat_core_parents_size:           -1
% 3.61/0.99  bmc1_merge_next_fun:                    0
% 3.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation
% 3.61/0.99  
% 3.61/0.99  inst_num_of_clauses:                    1391
% 3.61/0.99  inst_num_in_passive:                    875
% 3.61/0.99  inst_num_in_active:                     498
% 3.61/0.99  inst_num_in_unprocessed:                21
% 3.61/0.99  inst_num_of_loops:                      680
% 3.61/0.99  inst_num_of_learning_restarts:          0
% 3.61/0.99  inst_num_moves_active_passive:          180
% 3.61/0.99  inst_lit_activity:                      0
% 3.61/0.99  inst_lit_activity_moves:                0
% 3.61/0.99  inst_num_tautologies:                   0
% 3.61/0.99  inst_num_prop_implied:                  0
% 3.61/0.99  inst_num_existing_simplified:           0
% 3.61/0.99  inst_num_eq_res_simplified:             0
% 3.61/0.99  inst_num_child_elim:                    0
% 3.61/0.99  inst_num_of_dismatching_blockings:      454
% 3.61/0.99  inst_num_of_non_proper_insts:           1389
% 3.61/0.99  inst_num_of_duplicates:                 0
% 3.61/0.99  inst_inst_num_from_inst_to_res:         0
% 3.61/0.99  inst_dismatching_checking_time:         0.
% 3.61/0.99  
% 3.61/0.99  ------ Resolution
% 3.61/0.99  
% 3.61/0.99  res_num_of_clauses:                     0
% 3.61/0.99  res_num_in_passive:                     0
% 3.61/0.99  res_num_in_active:                      0
% 3.61/0.99  res_num_of_loops:                       140
% 3.61/0.99  res_forward_subset_subsumed:            50
% 3.61/0.99  res_backward_subset_subsumed:           6
% 3.61/0.99  res_forward_subsumed:                   0
% 3.61/0.99  res_backward_subsumed:                  0
% 3.61/0.99  res_forward_subsumption_resolution:     0
% 3.61/0.99  res_backward_subsumption_resolution:    0
% 3.61/0.99  res_clause_to_clause_subsumption:       691
% 3.61/0.99  res_orphan_elimination:                 0
% 3.61/0.99  res_tautology_del:                      93
% 3.61/0.99  res_num_eq_res_simplified:              1
% 3.61/0.99  res_num_sel_changes:                    0
% 3.61/0.99  res_moves_from_active_to_pass:          0
% 3.61/0.99  
% 3.61/0.99  ------ Superposition
% 3.61/0.99  
% 3.61/0.99  sup_time_total:                         0.
% 3.61/0.99  sup_time_generating:                    0.
% 3.61/0.99  sup_time_sim_full:                      0.
% 3.61/0.99  sup_time_sim_immed:                     0.
% 3.61/0.99  
% 3.61/0.99  sup_num_of_clauses:                     159
% 3.61/0.99  sup_num_in_active:                      65
% 3.61/0.99  sup_num_in_passive:                     94
% 3.61/0.99  sup_num_of_loops:                       134
% 3.61/0.99  sup_fw_superposition:                   154
% 3.61/0.99  sup_bw_superposition:                   100
% 3.61/0.99  sup_immediate_simplified:               87
% 3.61/0.99  sup_given_eliminated:                   1
% 3.61/0.99  comparisons_done:                       0
% 3.61/0.99  comparisons_avoided:                    84
% 3.61/0.99  
% 3.61/0.99  ------ Simplifications
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  sim_fw_subset_subsumed:                 20
% 3.61/0.99  sim_bw_subset_subsumed:                 19
% 3.61/0.99  sim_fw_subsumed:                        13
% 3.61/0.99  sim_bw_subsumed:                        0
% 3.61/0.99  sim_fw_subsumption_res:                 13
% 3.61/0.99  sim_bw_subsumption_res:                 0
% 3.61/0.99  sim_tautology_del:                      5
% 3.61/0.99  sim_eq_tautology_del:                   31
% 3.61/0.99  sim_eq_res_simp:                        7
% 3.61/0.99  sim_fw_demodulated:                     25
% 3.61/0.99  sim_bw_demodulated:                     57
% 3.61/0.99  sim_light_normalised:                   34
% 3.61/0.99  sim_joinable_taut:                      0
% 3.61/0.99  sim_joinable_simp:                      0
% 3.61/0.99  sim_ac_normalised:                      0
% 3.61/0.99  sim_smt_subsumption:                    0
% 3.61/0.99  
%------------------------------------------------------------------------------
