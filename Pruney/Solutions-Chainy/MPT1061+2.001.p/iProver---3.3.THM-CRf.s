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
% DateTime   : Thu Dec  3 12:09:29 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  280 (3273 expanded)
%              Number of clauses        :  196 (1230 expanded)
%              Number of leaves         :   28 ( 759 expanded)
%              Depth                    :   32
%              Number of atoms          :  817 (18008 expanded)
%              Number of equality atoms :  464 (2762 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f50,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f50])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK4,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK4,X0,X3)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f51,f57,f56])).

fof(f94,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f90,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f103,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1298,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1297,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1305,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2347,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1297,c_1305])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_479,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_34])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_401,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_37])).

cnf(c_820,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1363,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1386,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_819,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1419,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1434,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_401,c_1386,c_1419])).

cnf(c_2350,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2347,c_1434])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1306,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2977,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_1306])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1933,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1934,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2491,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1313])).

cnf(c_3021,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2977,c_1934,c_2491])).

cnf(c_3022,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3021])).

cnf(c_3028,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1298,c_3022])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1307,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3071,plain,
    ( r1_tarski(sK1,sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_1307])).

cnf(c_3078,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3071,c_1934,c_2491])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1304,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2824,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1297,c_1304])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1299,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2985,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_1299])).

cnf(c_2812,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_1305])).

cnf(c_19088,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_2812])).

cnf(c_19225,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19088,c_3028])).

cnf(c_2571,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_1934])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1309,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2576,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2571,c_1309])).

cnf(c_19226,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19225,c_2576])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2304,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2305,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_19688,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19226,c_1934,c_2305,c_2491])).

cnf(c_19689,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19688])).

cnf(c_19692,plain,
    ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_19689])).

cnf(c_19696,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3078,c_19692])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1300,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3783,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1300])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3925,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3783,c_39])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_463,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1294,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_464,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1365,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1364])).

cnf(c_1501,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_39,c_41,c_464,c_1365])).

cnf(c_1502,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1501])).

cnf(c_3932,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3925,c_1502])).

cnf(c_19971,plain,
    ( sK2 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19696,c_3932])).

cnf(c_19983,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19971])).

cnf(c_19985,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_19983])).

cnf(c_19986,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19985,c_3028])).

cnf(c_19987,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19986,c_2576])).

cnf(c_19990,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19987,c_1934,c_2305,c_2491,c_2985,c_3071])).

cnf(c_19998,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19990,c_2985])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2809,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1303])).

cnf(c_4235,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_2809])).

cnf(c_4246,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4235,c_2576])).

cnf(c_4953,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4246,c_1934,c_2305,c_2491])).

cnf(c_4954,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4953])).

cnf(c_4959,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_4954])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_389,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_390,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_410,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_390])).

cnf(c_411,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_411,c_26])).

cnf(c_1295,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1318,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1295,c_3])).

cnf(c_1319,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1318,c_3])).

cnf(c_5061,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4959,c_1319])).

cnf(c_20115,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19998,c_5061])).

cnf(c_2349,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1305])).

cnf(c_5064,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4959,c_2349])).

cnf(c_5068,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5064,c_3028])).

cnf(c_20118,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_19998,c_5068])).

cnf(c_20168,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20115,c_20118])).

cnf(c_2810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1303])).

cnf(c_4415,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2576,c_2810])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1302,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3941,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3925,c_1302])).

cnf(c_4067,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3941,c_39,c_41])).

cnf(c_4074,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_1313])).

cnf(c_5476,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_1934,c_4074])).

cnf(c_5477,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5476])).

cnf(c_5483,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_5477])).

cnf(c_5501,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_5483])).

cnf(c_2333,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k2_partfun1(k1_xboole_0,X1,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1302])).

cnf(c_2335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(k1_xboole_0,X1,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2333,c_3])).

cnf(c_3298,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_1313])).

cnf(c_1311,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1660,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1311])).

cnf(c_8102,plain,
    ( v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3298,c_1660])).

cnf(c_8103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8102])).

cnf(c_3027,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(X0,sK0)))) = k1_relat_1(k7_relat_1(X0,sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1307,c_3022])).

cnf(c_8122,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,X1,X2),sK0)))) = k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,X1,X2),sK0))
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8103,c_3027])).

cnf(c_10385,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,k7_relat_1(sK4,sK1),X1),sK0)))) = k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,k7_relat_1(sK4,sK1),X1),sK0))
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5501,c_8122])).

cnf(c_1372,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1388,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1421,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1462,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1525,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1526,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1727,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1728,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1727])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1310,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2577,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2571,c_1310])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_31])).

cnf(c_522,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_817,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | sP0_iProver_split
    | sK1 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_522])).

cnf(c_1291,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_1320,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1291,c_3])).

cnf(c_816,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_522])).

cnf(c_1292,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_1316,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1292,c_3])).

cnf(c_1816,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_39,c_41,c_1316,c_1365])).

cnf(c_3928,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3925,c_1816])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1577,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_2220,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k7_relat_1(sK4,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_2704,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,X0),X1)
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_2220])).

cnf(c_4635,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2704])).

cnf(c_4636,plain,
    ( k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4635])).

cnf(c_4638,plain,
    ( k7_relat_1(sK4,sK1) != k7_relat_1(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4636])).

cnf(c_827,plain,
    ( X0 != X1
    | k7_relat_1(X2,X0) = k7_relat_1(X2,X1) ),
    theory(equality)).

cnf(c_4730,plain,
    ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,X0)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_4731,plain,
    ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4730])).

cnf(c_5393,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k7_relat_1(sK4,X2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_10233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k7_relat_1(sK4,X1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5393])).

cnf(c_10234,plain,
    ( k7_relat_1(sK4,X0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10233])).

cnf(c_10236,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10234])).

cnf(c_10434,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10385,c_1388,c_1421,c_1462,c_1526,c_1728,c_2577,c_3928,c_4638,c_4731,c_5501,c_10236])).

cnf(c_831,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3228,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | X0 != k2_partfun1(sK0,sK3,sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_6837,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | v1_funct_1(k7_relat_1(sK4,sK1))
    | k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_3228])).

cnf(c_6839,plain,
    ( k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1)
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6837])).

cnf(c_2056,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK3,sK4,sK1)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_3036,plain,
    ( X0 = k2_partfun1(sK0,sK3,sK4,sK1)
    | X0 != k7_relat_1(sK4,sK1)
    | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_4400,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
    | k7_relat_1(sK4,sK1) = k2_partfun1(sK0,sK3,sK4,sK1)
    | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_4339,plain,
    ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_2580,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_1307])).

cnf(c_1315,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2013,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1307,c_1315])).

cnf(c_2206,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_2013])).

cnf(c_1877,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_1310])).

cnf(c_2207,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2206,c_1877])).

cnf(c_2582,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2580,c_2207])).

cnf(c_821,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1717,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_1718,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(c_1720,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_120,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_119,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20168,c_10434,c_6839,c_4400,c_4339,c_2582,c_2491,c_1934,c_1720,c_1639,c_1365,c_120,c_119,c_41,c_34,c_39,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n006.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 11.52/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.52/2.00  
% 11.52/2.00  ------  iProver source info
% 11.52/2.00  
% 11.52/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.52/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.52/2.00  git: non_committed_changes: false
% 11.52/2.00  git: last_make_outside_of_git: false
% 11.52/2.00  
% 11.52/2.00  ------ 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options
% 11.52/2.00  
% 11.52/2.00  --out_options                           all
% 11.52/2.00  --tptp_safe_out                         true
% 11.52/2.00  --problem_path                          ""
% 11.52/2.00  --include_path                          ""
% 11.52/2.00  --clausifier                            res/vclausify_rel
% 11.52/2.00  --clausifier_options                    ""
% 11.52/2.00  --stdin                                 false
% 11.52/2.00  --stats_out                             all
% 11.52/2.00  
% 11.52/2.00  ------ General Options
% 11.52/2.00  
% 11.52/2.00  --fof                                   false
% 11.52/2.00  --time_out_real                         305.
% 11.52/2.00  --time_out_virtual                      -1.
% 11.52/2.00  --symbol_type_check                     false
% 11.52/2.00  --clausify_out                          false
% 11.52/2.00  --sig_cnt_out                           false
% 11.52/2.00  --trig_cnt_out                          false
% 11.52/2.00  --trig_cnt_out_tolerance                1.
% 11.52/2.00  --trig_cnt_out_sk_spl                   false
% 11.52/2.00  --abstr_cl_out                          false
% 11.52/2.00  
% 11.52/2.00  ------ Global Options
% 11.52/2.00  
% 11.52/2.00  --schedule                              default
% 11.52/2.00  --add_important_lit                     false
% 11.52/2.00  --prop_solver_per_cl                    1000
% 11.52/2.00  --min_unsat_core                        false
% 11.52/2.00  --soft_assumptions                      false
% 11.52/2.00  --soft_lemma_size                       3
% 11.52/2.00  --prop_impl_unit_size                   0
% 11.52/2.00  --prop_impl_unit                        []
% 11.52/2.00  --share_sel_clauses                     true
% 11.52/2.00  --reset_solvers                         false
% 11.52/2.00  --bc_imp_inh                            [conj_cone]
% 11.52/2.00  --conj_cone_tolerance                   3.
% 11.52/2.00  --extra_neg_conj                        none
% 11.52/2.00  --large_theory_mode                     true
% 11.52/2.00  --prolific_symb_bound                   200
% 11.52/2.00  --lt_threshold                          2000
% 11.52/2.00  --clause_weak_htbl                      true
% 11.52/2.00  --gc_record_bc_elim                     false
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing Options
% 11.52/2.00  
% 11.52/2.00  --preprocessing_flag                    true
% 11.52/2.00  --time_out_prep_mult                    0.1
% 11.52/2.00  --splitting_mode                        input
% 11.52/2.00  --splitting_grd                         true
% 11.52/2.00  --splitting_cvd                         false
% 11.52/2.00  --splitting_cvd_svl                     false
% 11.52/2.00  --splitting_nvd                         32
% 11.52/2.00  --sub_typing                            true
% 11.52/2.00  --prep_gs_sim                           true
% 11.52/2.00  --prep_unflatten                        true
% 11.52/2.00  --prep_res_sim                          true
% 11.52/2.00  --prep_upred                            true
% 11.52/2.00  --prep_sem_filter                       exhaustive
% 11.52/2.00  --prep_sem_filter_out                   false
% 11.52/2.00  --pred_elim                             true
% 11.52/2.00  --res_sim_input                         true
% 11.52/2.00  --eq_ax_congr_red                       true
% 11.52/2.00  --pure_diseq_elim                       true
% 11.52/2.00  --brand_transform                       false
% 11.52/2.00  --non_eq_to_eq                          false
% 11.52/2.00  --prep_def_merge                        true
% 11.52/2.00  --prep_def_merge_prop_impl              false
% 11.52/2.00  --prep_def_merge_mbd                    true
% 11.52/2.00  --prep_def_merge_tr_red                 false
% 11.52/2.00  --prep_def_merge_tr_cl                  false
% 11.52/2.00  --smt_preprocessing                     true
% 11.52/2.00  --smt_ac_axioms                         fast
% 11.52/2.00  --preprocessed_out                      false
% 11.52/2.00  --preprocessed_stats                    false
% 11.52/2.00  
% 11.52/2.00  ------ Abstraction refinement Options
% 11.52/2.00  
% 11.52/2.00  --abstr_ref                             []
% 11.52/2.00  --abstr_ref_prep                        false
% 11.52/2.00  --abstr_ref_until_sat                   false
% 11.52/2.00  --abstr_ref_sig_restrict                funpre
% 11.52/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.00  --abstr_ref_under                       []
% 11.52/2.00  
% 11.52/2.00  ------ SAT Options
% 11.52/2.00  
% 11.52/2.00  --sat_mode                              false
% 11.52/2.00  --sat_fm_restart_options                ""
% 11.52/2.00  --sat_gr_def                            false
% 11.52/2.00  --sat_epr_types                         true
% 11.52/2.00  --sat_non_cyclic_types                  false
% 11.52/2.00  --sat_finite_models                     false
% 11.52/2.00  --sat_fm_lemmas                         false
% 11.52/2.00  --sat_fm_prep                           false
% 11.52/2.00  --sat_fm_uc_incr                        true
% 11.52/2.00  --sat_out_model                         small
% 11.52/2.00  --sat_out_clauses                       false
% 11.52/2.00  
% 11.52/2.00  ------ QBF Options
% 11.52/2.00  
% 11.52/2.00  --qbf_mode                              false
% 11.52/2.00  --qbf_elim_univ                         false
% 11.52/2.00  --qbf_dom_inst                          none
% 11.52/2.00  --qbf_dom_pre_inst                      false
% 11.52/2.00  --qbf_sk_in                             false
% 11.52/2.00  --qbf_pred_elim                         true
% 11.52/2.00  --qbf_split                             512
% 11.52/2.00  
% 11.52/2.00  ------ BMC1 Options
% 11.52/2.00  
% 11.52/2.00  --bmc1_incremental                      false
% 11.52/2.00  --bmc1_axioms                           reachable_all
% 11.52/2.00  --bmc1_min_bound                        0
% 11.52/2.00  --bmc1_max_bound                        -1
% 11.52/2.00  --bmc1_max_bound_default                -1
% 11.52/2.00  --bmc1_symbol_reachability              true
% 11.52/2.00  --bmc1_property_lemmas                  false
% 11.52/2.00  --bmc1_k_induction                      false
% 11.52/2.00  --bmc1_non_equiv_states                 false
% 11.52/2.00  --bmc1_deadlock                         false
% 11.52/2.00  --bmc1_ucm                              false
% 11.52/2.00  --bmc1_add_unsat_core                   none
% 11.52/2.00  --bmc1_unsat_core_children              false
% 11.52/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.00  --bmc1_out_stat                         full
% 11.52/2.00  --bmc1_ground_init                      false
% 11.52/2.00  --bmc1_pre_inst_next_state              false
% 11.52/2.00  --bmc1_pre_inst_state                   false
% 11.52/2.00  --bmc1_pre_inst_reach_state             false
% 11.52/2.00  --bmc1_out_unsat_core                   false
% 11.52/2.00  --bmc1_aig_witness_out                  false
% 11.52/2.00  --bmc1_verbose                          false
% 11.52/2.00  --bmc1_dump_clauses_tptp                false
% 11.52/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.00  --bmc1_dump_file                        -
% 11.52/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.00  --bmc1_ucm_extend_mode                  1
% 11.52/2.00  --bmc1_ucm_init_mode                    2
% 11.52/2.00  --bmc1_ucm_cone_mode                    none
% 11.52/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.00  --bmc1_ucm_relax_model                  4
% 11.52/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.00  --bmc1_ucm_layered_model                none
% 11.52/2.00  --bmc1_ucm_max_lemma_size               10
% 11.52/2.00  
% 11.52/2.00  ------ AIG Options
% 11.52/2.00  
% 11.52/2.00  --aig_mode                              false
% 11.52/2.00  
% 11.52/2.00  ------ Instantiation Options
% 11.52/2.00  
% 11.52/2.00  --instantiation_flag                    true
% 11.52/2.00  --inst_sos_flag                         true
% 11.52/2.00  --inst_sos_phase                        true
% 11.52/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel_side                     num_symb
% 11.52/2.00  --inst_solver_per_active                1400
% 11.52/2.00  --inst_solver_calls_frac                1.
% 11.52/2.00  --inst_passive_queue_type               priority_queues
% 11.52/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.00  --inst_passive_queues_freq              [25;2]
% 11.52/2.00  --inst_dismatching                      true
% 11.52/2.00  --inst_eager_unprocessed_to_passive     true
% 11.52/2.00  --inst_prop_sim_given                   true
% 11.52/2.00  --inst_prop_sim_new                     false
% 11.52/2.00  --inst_subs_new                         false
% 11.52/2.00  --inst_eq_res_simp                      false
% 11.52/2.00  --inst_subs_given                       false
% 11.52/2.00  --inst_orphan_elimination               true
% 11.52/2.00  --inst_learning_loop_flag               true
% 11.52/2.00  --inst_learning_start                   3000
% 11.52/2.00  --inst_learning_factor                  2
% 11.52/2.00  --inst_start_prop_sim_after_learn       3
% 11.52/2.00  --inst_sel_renew                        solver
% 11.52/2.00  --inst_lit_activity_flag                true
% 11.52/2.00  --inst_restr_to_given                   false
% 11.52/2.00  --inst_activity_threshold               500
% 11.52/2.00  --inst_out_proof                        true
% 11.52/2.00  
% 11.52/2.00  ------ Resolution Options
% 11.52/2.00  
% 11.52/2.00  --resolution_flag                       true
% 11.52/2.00  --res_lit_sel                           adaptive
% 11.52/2.00  --res_lit_sel_side                      none
% 11.52/2.00  --res_ordering                          kbo
% 11.52/2.00  --res_to_prop_solver                    active
% 11.52/2.00  --res_prop_simpl_new                    false
% 11.52/2.00  --res_prop_simpl_given                  true
% 11.52/2.00  --res_passive_queue_type                priority_queues
% 11.52/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.00  --res_passive_queues_freq               [15;5]
% 11.52/2.00  --res_forward_subs                      full
% 11.52/2.00  --res_backward_subs                     full
% 11.52/2.00  --res_forward_subs_resolution           true
% 11.52/2.00  --res_backward_subs_resolution          true
% 11.52/2.00  --res_orphan_elimination                true
% 11.52/2.00  --res_time_limit                        2.
% 11.52/2.00  --res_out_proof                         true
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Options
% 11.52/2.00  
% 11.52/2.00  --superposition_flag                    true
% 11.52/2.00  --sup_passive_queue_type                priority_queues
% 11.52/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.00  --demod_completeness_check              fast
% 11.52/2.00  --demod_use_ground                      true
% 11.52/2.00  --sup_to_prop_solver                    passive
% 11.52/2.00  --sup_prop_simpl_new                    true
% 11.52/2.00  --sup_prop_simpl_given                  true
% 11.52/2.00  --sup_fun_splitting                     true
% 11.52/2.00  --sup_smt_interval                      50000
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Simplification Setup
% 11.52/2.00  
% 11.52/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.52/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.52/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.52/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.52/2.00  --sup_immed_triv                        [TrivRules]
% 11.52/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_bw_main                     []
% 11.52/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.52/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_input_bw                          []
% 11.52/2.00  
% 11.52/2.00  ------ Combination Options
% 11.52/2.00  
% 11.52/2.00  --comb_res_mult                         3
% 11.52/2.00  --comb_sup_mult                         2
% 11.52/2.00  --comb_inst_mult                        10
% 11.52/2.00  
% 11.52/2.00  ------ Debug Options
% 11.52/2.00  
% 11.52/2.00  --dbg_backtrace                         false
% 11.52/2.00  --dbg_dump_prop_clauses                 false
% 11.52/2.00  --dbg_dump_prop_clauses_file            -
% 11.52/2.00  --dbg_out_stat                          false
% 11.52/2.00  ------ Parsing...
% 11.52/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.52/2.00  ------ Proving...
% 11.52/2.00  ------ Problem Properties 
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  clauses                                 33
% 11.52/2.00  conjectures                             4
% 11.52/2.00  EPR                                     4
% 11.52/2.00  Horn                                    31
% 11.52/2.00  unary                                   9
% 11.52/2.00  binary                                  9
% 11.52/2.00  lits                                    84
% 11.52/2.00  lits eq                                 31
% 11.52/2.00  fd_pure                                 0
% 11.52/2.00  fd_pseudo                               0
% 11.52/2.00  fd_cond                                 3
% 11.52/2.00  fd_pseudo_cond                          0
% 11.52/2.00  AC symbols                              0
% 11.52/2.00  
% 11.52/2.00  ------ Schedule dynamic 5 is on 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  ------ 
% 11.52/2.00  Current options:
% 11.52/2.00  ------ 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options
% 11.52/2.00  
% 11.52/2.00  --out_options                           all
% 11.52/2.00  --tptp_safe_out                         true
% 11.52/2.00  --problem_path                          ""
% 11.52/2.00  --include_path                          ""
% 11.52/2.00  --clausifier                            res/vclausify_rel
% 11.52/2.00  --clausifier_options                    ""
% 11.52/2.00  --stdin                                 false
% 11.52/2.00  --stats_out                             all
% 11.52/2.00  
% 11.52/2.00  ------ General Options
% 11.52/2.00  
% 11.52/2.00  --fof                                   false
% 11.52/2.00  --time_out_real                         305.
% 11.52/2.00  --time_out_virtual                      -1.
% 11.52/2.00  --symbol_type_check                     false
% 11.52/2.00  --clausify_out                          false
% 11.52/2.00  --sig_cnt_out                           false
% 11.52/2.00  --trig_cnt_out                          false
% 11.52/2.00  --trig_cnt_out_tolerance                1.
% 11.52/2.00  --trig_cnt_out_sk_spl                   false
% 11.52/2.00  --abstr_cl_out                          false
% 11.52/2.00  
% 11.52/2.00  ------ Global Options
% 11.52/2.00  
% 11.52/2.00  --schedule                              default
% 11.52/2.00  --add_important_lit                     false
% 11.52/2.00  --prop_solver_per_cl                    1000
% 11.52/2.00  --min_unsat_core                        false
% 11.52/2.00  --soft_assumptions                      false
% 11.52/2.00  --soft_lemma_size                       3
% 11.52/2.00  --prop_impl_unit_size                   0
% 11.52/2.00  --prop_impl_unit                        []
% 11.52/2.00  --share_sel_clauses                     true
% 11.52/2.00  --reset_solvers                         false
% 11.52/2.00  --bc_imp_inh                            [conj_cone]
% 11.52/2.00  --conj_cone_tolerance                   3.
% 11.52/2.00  --extra_neg_conj                        none
% 11.52/2.00  --large_theory_mode                     true
% 11.52/2.00  --prolific_symb_bound                   200
% 11.52/2.00  --lt_threshold                          2000
% 11.52/2.00  --clause_weak_htbl                      true
% 11.52/2.00  --gc_record_bc_elim                     false
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing Options
% 11.52/2.00  
% 11.52/2.00  --preprocessing_flag                    true
% 11.52/2.00  --time_out_prep_mult                    0.1
% 11.52/2.00  --splitting_mode                        input
% 11.52/2.00  --splitting_grd                         true
% 11.52/2.00  --splitting_cvd                         false
% 11.52/2.00  --splitting_cvd_svl                     false
% 11.52/2.00  --splitting_nvd                         32
% 11.52/2.00  --sub_typing                            true
% 11.52/2.00  --prep_gs_sim                           true
% 11.52/2.00  --prep_unflatten                        true
% 11.52/2.00  --prep_res_sim                          true
% 11.52/2.00  --prep_upred                            true
% 11.52/2.00  --prep_sem_filter                       exhaustive
% 11.52/2.00  --prep_sem_filter_out                   false
% 11.52/2.00  --pred_elim                             true
% 11.52/2.00  --res_sim_input                         true
% 11.52/2.00  --eq_ax_congr_red                       true
% 11.52/2.00  --pure_diseq_elim                       true
% 11.52/2.00  --brand_transform                       false
% 11.52/2.00  --non_eq_to_eq                          false
% 11.52/2.00  --prep_def_merge                        true
% 11.52/2.00  --prep_def_merge_prop_impl              false
% 11.52/2.00  --prep_def_merge_mbd                    true
% 11.52/2.00  --prep_def_merge_tr_red                 false
% 11.52/2.00  --prep_def_merge_tr_cl                  false
% 11.52/2.00  --smt_preprocessing                     true
% 11.52/2.00  --smt_ac_axioms                         fast
% 11.52/2.00  --preprocessed_out                      false
% 11.52/2.00  --preprocessed_stats                    false
% 11.52/2.00  
% 11.52/2.00  ------ Abstraction refinement Options
% 11.52/2.00  
% 11.52/2.00  --abstr_ref                             []
% 11.52/2.00  --abstr_ref_prep                        false
% 11.52/2.00  --abstr_ref_until_sat                   false
% 11.52/2.00  --abstr_ref_sig_restrict                funpre
% 11.52/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.00  --abstr_ref_under                       []
% 11.52/2.00  
% 11.52/2.00  ------ SAT Options
% 11.52/2.00  
% 11.52/2.00  --sat_mode                              false
% 11.52/2.00  --sat_fm_restart_options                ""
% 11.52/2.00  --sat_gr_def                            false
% 11.52/2.00  --sat_epr_types                         true
% 11.52/2.00  --sat_non_cyclic_types                  false
% 11.52/2.00  --sat_finite_models                     false
% 11.52/2.00  --sat_fm_lemmas                         false
% 11.52/2.00  --sat_fm_prep                           false
% 11.52/2.00  --sat_fm_uc_incr                        true
% 11.52/2.00  --sat_out_model                         small
% 11.52/2.00  --sat_out_clauses                       false
% 11.52/2.00  
% 11.52/2.00  ------ QBF Options
% 11.52/2.00  
% 11.52/2.00  --qbf_mode                              false
% 11.52/2.00  --qbf_elim_univ                         false
% 11.52/2.00  --qbf_dom_inst                          none
% 11.52/2.00  --qbf_dom_pre_inst                      false
% 11.52/2.00  --qbf_sk_in                             false
% 11.52/2.00  --qbf_pred_elim                         true
% 11.52/2.00  --qbf_split                             512
% 11.52/2.00  
% 11.52/2.00  ------ BMC1 Options
% 11.52/2.00  
% 11.52/2.00  --bmc1_incremental                      false
% 11.52/2.00  --bmc1_axioms                           reachable_all
% 11.52/2.00  --bmc1_min_bound                        0
% 11.52/2.00  --bmc1_max_bound                        -1
% 11.52/2.00  --bmc1_max_bound_default                -1
% 11.52/2.00  --bmc1_symbol_reachability              true
% 11.52/2.00  --bmc1_property_lemmas                  false
% 11.52/2.00  --bmc1_k_induction                      false
% 11.52/2.00  --bmc1_non_equiv_states                 false
% 11.52/2.00  --bmc1_deadlock                         false
% 11.52/2.00  --bmc1_ucm                              false
% 11.52/2.00  --bmc1_add_unsat_core                   none
% 11.52/2.00  --bmc1_unsat_core_children              false
% 11.52/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.00  --bmc1_out_stat                         full
% 11.52/2.00  --bmc1_ground_init                      false
% 11.52/2.00  --bmc1_pre_inst_next_state              false
% 11.52/2.00  --bmc1_pre_inst_state                   false
% 11.52/2.00  --bmc1_pre_inst_reach_state             false
% 11.52/2.00  --bmc1_out_unsat_core                   false
% 11.52/2.00  --bmc1_aig_witness_out                  false
% 11.52/2.00  --bmc1_verbose                          false
% 11.52/2.00  --bmc1_dump_clauses_tptp                false
% 11.52/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.00  --bmc1_dump_file                        -
% 11.52/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.00  --bmc1_ucm_extend_mode                  1
% 11.52/2.00  --bmc1_ucm_init_mode                    2
% 11.52/2.00  --bmc1_ucm_cone_mode                    none
% 11.52/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.00  --bmc1_ucm_relax_model                  4
% 11.52/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.00  --bmc1_ucm_layered_model                none
% 11.52/2.00  --bmc1_ucm_max_lemma_size               10
% 11.52/2.00  
% 11.52/2.00  ------ AIG Options
% 11.52/2.00  
% 11.52/2.00  --aig_mode                              false
% 11.52/2.00  
% 11.52/2.00  ------ Instantiation Options
% 11.52/2.00  
% 11.52/2.00  --instantiation_flag                    true
% 11.52/2.00  --inst_sos_flag                         true
% 11.52/2.00  --inst_sos_phase                        true
% 11.52/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel_side                     none
% 11.52/2.00  --inst_solver_per_active                1400
% 11.52/2.00  --inst_solver_calls_frac                1.
% 11.52/2.00  --inst_passive_queue_type               priority_queues
% 11.52/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.00  --inst_passive_queues_freq              [25;2]
% 11.52/2.00  --inst_dismatching                      true
% 11.52/2.00  --inst_eager_unprocessed_to_passive     true
% 11.52/2.00  --inst_prop_sim_given                   true
% 11.52/2.00  --inst_prop_sim_new                     false
% 11.52/2.00  --inst_subs_new                         false
% 11.52/2.00  --inst_eq_res_simp                      false
% 11.52/2.00  --inst_subs_given                       false
% 11.52/2.00  --inst_orphan_elimination               true
% 11.52/2.00  --inst_learning_loop_flag               true
% 11.52/2.00  --inst_learning_start                   3000
% 11.52/2.00  --inst_learning_factor                  2
% 11.52/2.00  --inst_start_prop_sim_after_learn       3
% 11.52/2.00  --inst_sel_renew                        solver
% 11.52/2.00  --inst_lit_activity_flag                true
% 11.52/2.00  --inst_restr_to_given                   false
% 11.52/2.00  --inst_activity_threshold               500
% 11.52/2.00  --inst_out_proof                        true
% 11.52/2.00  
% 11.52/2.00  ------ Resolution Options
% 11.52/2.00  
% 11.52/2.00  --resolution_flag                       false
% 11.52/2.00  --res_lit_sel                           adaptive
% 11.52/2.00  --res_lit_sel_side                      none
% 11.52/2.00  --res_ordering                          kbo
% 11.52/2.00  --res_to_prop_solver                    active
% 11.52/2.00  --res_prop_simpl_new                    false
% 11.52/2.00  --res_prop_simpl_given                  true
% 11.52/2.00  --res_passive_queue_type                priority_queues
% 11.52/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.00  --res_passive_queues_freq               [15;5]
% 11.52/2.00  --res_forward_subs                      full
% 11.52/2.00  --res_backward_subs                     full
% 11.52/2.00  --res_forward_subs_resolution           true
% 11.52/2.00  --res_backward_subs_resolution          true
% 11.52/2.00  --res_orphan_elimination                true
% 11.52/2.00  --res_time_limit                        2.
% 11.52/2.00  --res_out_proof                         true
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Options
% 11.52/2.00  
% 11.52/2.00  --superposition_flag                    true
% 11.52/2.00  --sup_passive_queue_type                priority_queues
% 11.52/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.00  --demod_completeness_check              fast
% 11.52/2.00  --demod_use_ground                      true
% 11.52/2.00  --sup_to_prop_solver                    passive
% 11.52/2.00  --sup_prop_simpl_new                    true
% 11.52/2.00  --sup_prop_simpl_given                  true
% 11.52/2.00  --sup_fun_splitting                     true
% 11.52/2.00  --sup_smt_interval                      50000
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Simplification Setup
% 11.52/2.00  
% 11.52/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.52/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.52/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.52/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.52/2.00  --sup_immed_triv                        [TrivRules]
% 11.52/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_bw_main                     []
% 11.52/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.52/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_input_bw                          []
% 11.52/2.00  
% 11.52/2.00  ------ Combination Options
% 11.52/2.00  
% 11.52/2.00  --comb_res_mult                         3
% 11.52/2.00  --comb_sup_mult                         2
% 11.52/2.00  --comb_inst_mult                        10
% 11.52/2.00  
% 11.52/2.00  ------ Debug Options
% 11.52/2.00  
% 11.52/2.00  --dbg_backtrace                         false
% 11.52/2.00  --dbg_dump_prop_clauses                 false
% 11.52/2.00  --dbg_dump_prop_clauses_file            -
% 11.52/2.00  --dbg_out_stat                          false
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  ------ Proving...
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  % SZS status Theorem for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  fof(f17,axiom,(
% 11.52/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f39,plain,(
% 11.52/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 11.52/2.00    inference(ennf_transformation,[],[f17])).
% 11.52/2.00  
% 11.52/2.00  fof(f40,plain,(
% 11.52/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 11.52/2.00    inference(flattening,[],[f39])).
% 11.52/2.00  
% 11.52/2.00  fof(f77,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f40])).
% 11.52/2.00  
% 11.52/2.00  fof(f23,conjecture,(
% 11.52/2.00    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f24,negated_conjecture,(
% 11.52/2.00    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 11.52/2.00    inference(negated_conjecture,[],[f23])).
% 11.52/2.00  
% 11.52/2.00  fof(f50,plain,(
% 11.52/2.00    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 11.52/2.00    inference(ennf_transformation,[],[f24])).
% 11.52/2.00  
% 11.52/2.00  fof(f51,plain,(
% 11.52/2.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 11.52/2.00    inference(flattening,[],[f50])).
% 11.52/2.00  
% 11.52/2.00  fof(f57,plain,(
% 11.52/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f56,plain,(
% 11.52/2.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f58,plain,(
% 11.52/2.00    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 11.52/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f51,f57,f56])).
% 11.52/2.00  
% 11.52/2.00  fof(f94,plain,(
% 11.52/2.00    r1_tarski(sK1,sK0)),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f93,plain,(
% 11.52/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f15,axiom,(
% 11.52/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f37,plain,(
% 11.52/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(ennf_transformation,[],[f15])).
% 11.52/2.00  
% 11.52/2.00  fof(f75,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f37])).
% 11.52/2.00  
% 11.52/2.00  fof(f20,axiom,(
% 11.52/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f44,plain,(
% 11.52/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(ennf_transformation,[],[f20])).
% 11.52/2.00  
% 11.52/2.00  fof(f45,plain,(
% 11.52/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(flattening,[],[f44])).
% 11.52/2.00  
% 11.52/2.00  fof(f55,plain,(
% 11.52/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(nnf_transformation,[],[f45])).
% 11.52/2.00  
% 11.52/2.00  fof(f81,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f55])).
% 11.52/2.00  
% 11.52/2.00  fof(f92,plain,(
% 11.52/2.00    v1_funct_2(sK4,sK0,sK3)),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f1,axiom,(
% 11.52/2.00    v1_xboole_0(k1_xboole_0)),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f59,plain,(
% 11.52/2.00    v1_xboole_0(k1_xboole_0)),
% 11.52/2.00    inference(cnf_transformation,[],[f1])).
% 11.52/2.00  
% 11.52/2.00  fof(f90,plain,(
% 11.52/2.00    ~v1_xboole_0(sK3)),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f14,axiom,(
% 11.52/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f35,plain,(
% 11.52/2.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.52/2.00    inference(ennf_transformation,[],[f14])).
% 11.52/2.00  
% 11.52/2.00  fof(f36,plain,(
% 11.52/2.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.52/2.00    inference(flattening,[],[f35])).
% 11.52/2.00  
% 11.52/2.00  fof(f74,plain,(
% 11.52/2.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f9,axiom,(
% 11.52/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f69,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f9])).
% 11.52/2.00  
% 11.52/2.00  fof(f6,axiom,(
% 11.52/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f27,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f6])).
% 11.52/2.00  
% 11.52/2.00  fof(f65,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f27])).
% 11.52/2.00  
% 11.52/2.00  fof(f13,axiom,(
% 11.52/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f34,plain,(
% 11.52/2.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.52/2.00    inference(ennf_transformation,[],[f13])).
% 11.52/2.00  
% 11.52/2.00  fof(f73,plain,(
% 11.52/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f34])).
% 11.52/2.00  
% 11.52/2.00  fof(f16,axiom,(
% 11.52/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f38,plain,(
% 11.52/2.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(ennf_transformation,[],[f16])).
% 11.52/2.00  
% 11.52/2.00  fof(f76,plain,(
% 11.52/2.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f38])).
% 11.52/2.00  
% 11.52/2.00  fof(f95,plain,(
% 11.52/2.00    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f11,axiom,(
% 11.52/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f31,plain,(
% 11.52/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.52/2.00    inference(ennf_transformation,[],[f11])).
% 11.52/2.00  
% 11.52/2.00  fof(f71,plain,(
% 11.52/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f31])).
% 11.52/2.00  
% 11.52/2.00  fof(f8,axiom,(
% 11.52/2.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f29,plain,(
% 11.52/2.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f8])).
% 11.52/2.00  
% 11.52/2.00  fof(f68,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f29])).
% 11.52/2.00  
% 11.52/2.00  fof(f22,axiom,(
% 11.52/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f48,plain,(
% 11.52/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.52/2.00    inference(ennf_transformation,[],[f22])).
% 11.52/2.00  
% 11.52/2.00  fof(f49,plain,(
% 11.52/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.52/2.00    inference(flattening,[],[f48])).
% 11.52/2.00  
% 11.52/2.00  fof(f89,plain,(
% 11.52/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f49])).
% 11.52/2.00  
% 11.52/2.00  fof(f91,plain,(
% 11.52/2.00    v1_funct_1(sK4)),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f83,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f55])).
% 11.52/2.00  
% 11.52/2.00  fof(f96,plain,(
% 11.52/2.00    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 11.52/2.00    inference(cnf_transformation,[],[f58])).
% 11.52/2.00  
% 11.52/2.00  fof(f21,axiom,(
% 11.52/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f46,plain,(
% 11.52/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.52/2.00    inference(ennf_transformation,[],[f21])).
% 11.52/2.00  
% 11.52/2.00  fof(f47,plain,(
% 11.52/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.52/2.00    inference(flattening,[],[f46])).
% 11.52/2.00  
% 11.52/2.00  fof(f87,plain,(
% 11.52/2.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f47])).
% 11.52/2.00  
% 11.52/2.00  fof(f3,axiom,(
% 11.52/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f52,plain,(
% 11.52/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.52/2.00    inference(nnf_transformation,[],[f3])).
% 11.52/2.00  
% 11.52/2.00  fof(f53,plain,(
% 11.52/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.52/2.00    inference(flattening,[],[f52])).
% 11.52/2.00  
% 11.52/2.00  fof(f63,plain,(
% 11.52/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.52/2.00    inference(cnf_transformation,[],[f53])).
% 11.52/2.00  
% 11.52/2.00  fof(f97,plain,(
% 11.52/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.52/2.00    inference(equality_resolution,[],[f63])).
% 11.52/2.00  
% 11.52/2.00  fof(f18,axiom,(
% 11.52/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f41,plain,(
% 11.52/2.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(ennf_transformation,[],[f18])).
% 11.52/2.00  
% 11.52/2.00  fof(f42,plain,(
% 11.52/2.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.00    inference(flattening,[],[f41])).
% 11.52/2.00  
% 11.52/2.00  fof(f79,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f42])).
% 11.52/2.00  
% 11.52/2.00  fof(f19,axiom,(
% 11.52/2.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f43,plain,(
% 11.52/2.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f19])).
% 11.52/2.00  
% 11.52/2.00  fof(f80,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f43])).
% 11.52/2.00  
% 11.52/2.00  fof(f82,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f55])).
% 11.52/2.00  
% 11.52/2.00  fof(f103,plain,(
% 11.52/2.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 11.52/2.00    inference(equality_resolution,[],[f82])).
% 11.52/2.00  
% 11.52/2.00  fof(f62,plain,(
% 11.52/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.52/2.00    inference(cnf_transformation,[],[f53])).
% 11.52/2.00  
% 11.52/2.00  fof(f98,plain,(
% 11.52/2.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.52/2.00    inference(equality_resolution,[],[f62])).
% 11.52/2.00  
% 11.52/2.00  fof(f88,plain,(
% 11.52/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f47])).
% 11.52/2.00  
% 11.52/2.00  fof(f2,axiom,(
% 11.52/2.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f26,plain,(
% 11.52/2.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.52/2.00    inference(ennf_transformation,[],[f2])).
% 11.52/2.00  
% 11.52/2.00  fof(f60,plain,(
% 11.52/2.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f26])).
% 11.52/2.00  
% 11.52/2.00  fof(f4,axiom,(
% 11.52/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f64,plain,(
% 11.52/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f4])).
% 11.52/2.00  
% 11.52/2.00  fof(f10,axiom,(
% 11.52/2.00    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 11.52/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f30,plain,(
% 11.52/2.00    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f10])).
% 11.52/2.00  
% 11.52/2.00  fof(f70,plain,(
% 11.52/2.00    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f30])).
% 11.52/2.00  
% 11.52/2.00  fof(f61,plain,(
% 11.52/2.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f53])).
% 11.52/2.00  
% 11.52/2.00  cnf(c_18,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.52/2.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 11.52/2.00      | ~ v1_relat_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1303,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.52/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_33,negated_conjecture,
% 11.52/2.00      ( r1_tarski(sK1,sK0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1298,plain,
% 11.52/2.00      ( r1_tarski(sK1,sK0) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_34,negated_conjecture,
% 11.52/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 11.52/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1297,plain,
% 11.52/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_16,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1305,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.52/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2347,plain,
% 11.52/2.00      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1297,c_1305]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_27,plain,
% 11.52/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.52/2.00      | k1_xboole_0 = X2 ),
% 11.52/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_35,negated_conjecture,
% 11.52/2.00      ( v1_funct_2(sK4,sK0,sK3) ),
% 11.52/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_478,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.52/2.00      | sK4 != X0
% 11.52/2.00      | sK3 != X2
% 11.52/2.00      | sK0 != X1
% 11.52/2.00      | k1_xboole_0 = X2 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_479,plain,
% 11.52/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 11.52/2.00      | k1_relset_1(sK0,sK3,sK4) = sK0
% 11.52/2.00      | k1_xboole_0 = sK3 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_478]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_481,plain,
% 11.52/2.00      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_479,c_34]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_0,plain,
% 11.52/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_37,negated_conjecture,
% 11.52/2.00      ( ~ v1_xboole_0(sK3) ),
% 11.52/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_401,plain,
% 11.52/2.00      ( sK3 != k1_xboole_0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_37]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_820,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1363,plain,
% 11.52/2.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_820]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1386,plain,
% 11.52/2.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1363]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_819,plain,( X0 = X0 ),theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1419,plain,
% 11.52/2.00      ( sK3 = sK3 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_819]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1434,plain,
% 11.52/2.00      ( k1_relset_1(sK0,sK3,sK4) = sK0 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_481,c_401,c_1386,c_1419]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2350,plain,
% 11.52/2.00      ( k1_relat_1(sK4) = sK0 ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_2347,c_1434]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_15,plain,
% 11.52/2.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.52/2.00      | ~ v1_relat_1(X1)
% 11.52/2.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1306,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.52/2.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2977,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 11.52/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.52/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2350,c_1306]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10,plain,
% 11.52/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.52/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1933,plain,
% 11.52/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1934,plain,
% 11.52/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_6,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.52/2.00      | ~ v1_relat_1(X1)
% 11.52/2.00      | v1_relat_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1313,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.52/2.00      | v1_relat_1(X1) != iProver_top
% 11.52/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2491,plain,
% 11.52/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 11.52/2.00      | v1_relat_1(sK4) = iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1297,c_1313]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3021,plain,
% 11.52/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.52/2.00      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_2977,c_1934,c_2491]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3022,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 11.52/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_3021]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3028,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1298,c_3022]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_14,plain,
% 11.52/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1307,plain,
% 11.52/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3071,plain,
% 11.52/2.00      ( r1_tarski(sK1,sK1) = iProver_top
% 11.52/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3028,c_1307]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3078,plain,
% 11.52/2.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_3071,c_1934,c_2491]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_17,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.52/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1304,plain,
% 11.52/2.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.52/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2824,plain,
% 11.52/2.00      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1297,c_1304]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_32,negated_conjecture,
% 11.52/2.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1299,plain,
% 11.52/2.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2985,plain,
% 11.52/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_2824,c_1299]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2812,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.52/2.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 11.52/2.00      | v1_relat_1(X2) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1303,c_1305]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19088,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 11.52/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3028,c_2812]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19225,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 11.52/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_19088,c_3028]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2571,plain,
% 11.52/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_2491,c_1934]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_12,plain,
% 11.52/2.00      ( ~ v1_relat_1(X0)
% 11.52/2.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1309,plain,
% 11.52/2.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2576,plain,
% 11.52/2.00      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2571,c_1309]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19226,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_19225,c_2576]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_9,plain,
% 11.52/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.52/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2304,plain,
% 11.52/2.00      ( v1_relat_1(k7_relat_1(sK4,sK1)) | ~ v1_relat_1(sK4) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2305,plain,
% 11.52/2.00      ( v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
% 11.52/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_2304]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19688,plain,
% 11.52/2.00      ( r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 11.52/2.00      | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_19226,c_1934,c_2305,c_2491]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19689,plain,
% 11.52/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_19688]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19692,plain,
% 11.52/2.00      ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2985,c_19689]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19696,plain,
% 11.52/2.00      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3078,c_19692]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_30,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0)
% 11.52/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.52/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1300,plain,
% 11.52/2.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.52/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.52/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3783,plain,
% 11.52/2.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 11.52/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1297,c_1300]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_36,negated_conjecture,
% 11.52/2.00      ( v1_funct_1(sK4) ),
% 11.52/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_39,plain,
% 11.52/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3925,plain,
% 11.52/2.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_3783,c_39]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_25,plain,
% 11.52/2.00      ( v1_funct_2(X0,X1,X2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k1_relset_1(X1,X2,X0) != X1
% 11.52/2.00      | k1_xboole_0 = X2 ),
% 11.52/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_31,negated_conjecture,
% 11.52/2.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 11.52/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_462,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 11.52/2.00      | k1_relset_1(X1,X2,X0) != X1
% 11.52/2.00      | sK2 != X2
% 11.52/2.00      | sK1 != X1
% 11.52/2.00      | k1_xboole_0 = X2 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_463,plain,
% 11.52/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 11.52/2.00      | k1_xboole_0 = sK2 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_462]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1294,plain,
% 11.52/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 11.52/2.00      | k1_xboole_0 = sK2
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_41,plain,
% 11.52/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_464,plain,
% 11.52/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 11.52/2.00      | k1_xboole_0 = sK2
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0)
% 11.52/2.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 11.52/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1364,plain,
% 11.52/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | ~ v1_funct_1(sK4) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_29]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1365,plain,
% 11.52/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 11.52/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1364]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1501,plain,
% 11.52/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | k1_xboole_0 = sK2
% 11.52/2.00      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_1294,c_39,c_41,c_464,c_1365]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1502,plain,
% 11.52/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 11.52/2.00      | k1_xboole_0 = sK2
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_1501]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3932,plain,
% 11.52/2.00      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
% 11.52/2.00      | sK2 = k1_xboole_0
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_3925,c_1502]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19971,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0
% 11.52/2.00      | sK1 != sK1
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_19696,c_3932]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19983,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(equality_resolution_simp,[status(thm)],[c_19971]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19985,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0
% 11.52/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1303,c_19983]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19986,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0
% 11.52/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_19985,c_3028]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19987,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_19986,c_2576]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19990,plain,
% 11.52/2.00      ( sK2 = k1_xboole_0 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_19987,c_1934,c_2305,c_2491,c_2985,c_3071]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19998,plain,
% 11.52/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_19990,c_2985]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2,plain,
% 11.52/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2809,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2,c_1303]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4235,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),k1_xboole_0) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3028,c_2809]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4246,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_4235,c_2576]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4953,plain,
% 11.52/2.00      ( r1_tarski(sK1,X0) != iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_4246,c_1934,c_2305,c_2491]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4954,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_4953]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4959,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1298,c_4954]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19,plain,
% 11.52/2.00      ( v1_funct_2(X0,X1,X2)
% 11.52/2.00      | ~ v1_partfun1(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_21,plain,
% 11.52/2.00      ( v1_partfun1(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ v1_xboole_0(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_389,plain,
% 11.52/2.00      ( v1_partfun1(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | k1_xboole_0 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_390,plain,
% 11.52/2.00      ( v1_partfun1(X0,k1_xboole_0)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_389]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_410,plain,
% 11.52/2.00      ( v1_funct_2(X0,X1,X2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 11.52/2.00      | ~ v1_funct_1(X0)
% 11.52/2.00      | X3 != X0
% 11.52/2.00      | k1_xboole_0 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_390]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_411,plain,
% 11.52/2.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_410]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_26,plain,
% 11.52/2.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.52/2.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_434,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0)
% 11.52/2.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 11.52/2.00      inference(resolution,[status(thm)],[c_411,c_26]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1295,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
% 11.52/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3,plain,
% 11.52/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1318,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_1295,c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1319,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_1318,c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5061,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_xboole_0
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_4959,c_1319]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_20115,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_xboole_0
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_19998,c_5061]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2349,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3,c_1305]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5064,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_4959,c_2349]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5068,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_5064,c_3028]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_20118,plain,
% 11.52/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_19998,c_5068]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_20168,plain,
% 11.52/2.00      ( sK1 = k1_xboole_0
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_20115,c_20118]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2810,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 11.52/2.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3,c_1303]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4415,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
% 11.52/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top
% 11.52/2.00      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2576,c_2810]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_28,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.00      | ~ v1_funct_1(X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1302,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3941,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 11.52/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 11.52/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3925,c_1302]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4067,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_3941,c_39,c_41]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4074,plain,
% 11.52/2.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 11.52/2.00      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_4067,c_1313]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5476,plain,
% 11.52/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_4415,c_1934,c_4074]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5477,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
% 11.52/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_5476]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5483,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X0) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3028,c_5477]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5501,plain,
% 11.52/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2985,c_5483]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2333,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(k1_xboole_0,X1,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3,c_1302]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2335,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(k1_xboole_0,X1,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_2333,c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3298,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top
% 11.52/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2335,c_1313]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1311,plain,
% 11.52/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1660,plain,
% 11.52/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2,c_1311]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_8102,plain,
% 11.52/2.00      ( v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_3298,c_1660]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_8103,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(X0) != iProver_top
% 11.52/2.00      | v1_relat_1(k2_partfun1(k1_xboole_0,X1,X0,X2)) = iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_8102]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3027,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(X0,sK0)))) = k1_relat_1(k7_relat_1(X0,sK0))
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1307,c_3022]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_8122,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,X1,X2),sK0)))) = k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,X1,X2),sK0))
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_8103,c_3027]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10385,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,k7_relat_1(sK4,sK1),X1),sK0)))) = k1_relat_1(k7_relat_1(k2_partfun1(k1_xboole_0,X0,k7_relat_1(sK4,sK1),X1),sK0))
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_5501,c_8122]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1372,plain,
% 11.52/2.00      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_820]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1388,plain,
% 11.52/2.00      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1372]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1421,plain,
% 11.52/2.00      ( sK1 = sK1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_819]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1462,plain,
% 11.52/2.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_819]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1,plain,
% 11.52/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1525,plain,
% 11.52/2.00      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1526,plain,
% 11.52/2.00      ( k1_xboole_0 = sK1 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5,plain,
% 11.52/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.52/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1727,plain,
% 11.52/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1728,plain,
% 11.52/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1727]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_11,plain,
% 11.52/2.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1310,plain,
% 11.52/2.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2577,plain,
% 11.52/2.00      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2571,c_1310]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_521,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ v1_funct_1(X0)
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 11.52/2.00      | sK2 != X1
% 11.52/2.00      | sK1 != k1_xboole_0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_411,c_31]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_522,plain,
% 11.52/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | sK1 != k1_xboole_0 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_521]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_817,plain,
% 11.52/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | sP0_iProver_split
% 11.52/2.00      | sK1 != k1_xboole_0 ),
% 11.52/2.00      inference(splitting,
% 11.52/2.00                [splitting(split),new_symbols(definition,[])],
% 11.52/2.00                [c_522]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1291,plain,
% 11.52/2.00      ( sK1 != k1_xboole_0
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 11.52/2.00      | sP0_iProver_split = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1320,plain,
% 11.52/2.00      ( sK1 != k1_xboole_0
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 11.52/2.00      | sP0_iProver_split = iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_1291,c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_816,plain,
% 11.52/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.52/2.00      | ~ sP0_iProver_split ),
% 11.52/2.00      inference(splitting,
% 11.52/2.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.52/2.00                [c_522]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1292,plain,
% 11.52/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.52/2.00      | sP0_iProver_split != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1316,plain,
% 11.52/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.52/2.00      | sP0_iProver_split != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_1292,c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1816,plain,
% 11.52/2.00      ( sK1 != k1_xboole_0
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_1320,c_39,c_41,c_1316,c_1365]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3928,plain,
% 11.52/2.00      ( sK1 != k1_xboole_0
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_3925,c_1816]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_824,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.52/2.00      theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1577,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,X1)
% 11.52/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | X2 != X0
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_824]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2220,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,X1)
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | k7_relat_1(sK4,sK1) != X0
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1577]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2704,plain,
% 11.52/2.00      ( ~ m1_subset_1(k7_relat_1(sK4,X0),X1)
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_2220]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4635,plain,
% 11.52/2.00      ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_2704]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4636,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) != k7_relat_1(sK4,X0)
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_4635]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4638,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) != k7_relat_1(sK4,k1_xboole_0)
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_4636]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_827,plain,
% 11.52/2.00      ( X0 != X1 | k7_relat_1(X2,X0) = k7_relat_1(X2,X1) ),
% 11.52/2.00      theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4730,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,X0) | sK1 != X0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_827]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4731,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,k1_xboole_0)
% 11.52/2.00      | sK1 != k1_xboole_0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_4730]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5393,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,X1)
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | k7_relat_1(sK4,X2) != X0
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1577]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10233,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.00      | k7_relat_1(sK4,X1) != X0
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_5393]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10234,plain,
% 11.52/2.00      ( k7_relat_1(sK4,X0) != X1
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_10233]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10236,plain,
% 11.52/2.00      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 11.52/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 11.52/2.00      | m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 11.52/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_10234]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10434,plain,
% 11.52/2.00      ( r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_10385,c_1388,c_1421,c_1462,c_1526,c_1728,c_2577,
% 11.52/2.00                 c_3928,c_4638,c_4731,c_5501,c_10236]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_831,plain,
% 11.52/2.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.52/2.00      theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3228,plain,
% 11.52/2.00      ( v1_funct_1(X0)
% 11.52/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | X0 != k2_partfun1(sK0,sK3,sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_6837,plain,
% 11.52/2.00      ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1))
% 11.52/2.00      | k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_3228]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_6839,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1)
% 11.52/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 11.52/2.00      | v1_funct_1(k7_relat_1(sK4,sK1)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_6837]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2056,plain,
% 11.52/2.00      ( X0 != X1
% 11.52/2.00      | X0 = k2_partfun1(sK0,sK3,sK4,sK1)
% 11.52/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_820]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3036,plain,
% 11.52/2.00      ( X0 = k2_partfun1(sK0,sK3,sK4,sK1)
% 11.52/2.00      | X0 != k7_relat_1(sK4,sK1)
% 11.52/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_2056]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4400,plain,
% 11.52/2.00      ( k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
% 11.52/2.00      | k7_relat_1(sK4,sK1) = k2_partfun1(sK0,sK3,sK4,sK1)
% 11.52/2.00      | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_3036]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4339,plain,
% 11.52/2.00      ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_819]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2580,plain,
% 11.52/2.00      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 11.52/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2577,c_1307]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1315,plain,
% 11.52/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2013,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.52/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1307,c_1315]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2206,plain,
% 11.52/2.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1660,c_2013]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1877,plain,
% 11.52/2.00      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1660,c_1310]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2207,plain,
% 11.52/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_2206,c_1877]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2582,plain,
% 11.52/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 11.52/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_2580,c_2207]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_821,plain,
% 11.52/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.52/2.00      theory(equality) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1717,plain,
% 11.52/2.00      ( ~ r1_tarski(X0,X1)
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0)
% 11.52/2.00      | sK1 != X0
% 11.52/2.00      | k1_xboole_0 != X1 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_821]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1718,plain,
% 11.52/2.00      ( sK1 != X0
% 11.52/2.00      | k1_xboole_0 != X1
% 11.52/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_1717]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1720,plain,
% 11.52/2.00      ( sK1 != k1_xboole_0
% 11.52/2.00      | k1_xboole_0 != k1_xboole_0
% 11.52/2.00      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 11.52/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1718]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1639,plain,
% 11.52/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 11.52/2.00      | ~ v1_funct_1(sK4)
% 11.52/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_30]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_120,plain,
% 11.52/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4,plain,
% 11.52/2.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.52/2.00      | k1_xboole_0 = X0
% 11.52/2.00      | k1_xboole_0 = X1 ),
% 11.52/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_119,plain,
% 11.52/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.52/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(contradiction,plain,
% 11.52/2.00      ( $false ),
% 11.52/2.00      inference(minisat,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_20168,c_10434,c_6839,c_4400,c_4339,c_2582,c_2491,
% 11.52/2.00                 c_1934,c_1720,c_1639,c_1365,c_120,c_119,c_41,c_34,c_39,
% 11.52/2.00                 c_36]) ).
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  ------                               Statistics
% 11.52/2.00  
% 11.52/2.00  ------ General
% 11.52/2.00  
% 11.52/2.00  abstr_ref_over_cycles:                  0
% 11.52/2.00  abstr_ref_under_cycles:                 0
% 11.52/2.00  gc_basic_clause_elim:                   0
% 11.52/2.00  forced_gc_time:                         0
% 11.52/2.00  parsing_time:                           0.008
% 11.52/2.00  unif_index_cands_time:                  0.
% 11.52/2.00  unif_index_add_time:                    0.
% 11.52/2.00  orderings_time:                         0.
% 11.52/2.00  out_proof_time:                         0.018
% 11.52/2.00  total_time:                             1.006
% 11.52/2.00  num_of_symbols:                         55
% 11.52/2.00  num_of_terms:                           35983
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing
% 11.52/2.00  
% 11.52/2.00  num_of_splits:                          1
% 11.52/2.00  num_of_split_atoms:                     1
% 11.52/2.00  num_of_reused_defs:                     0
% 11.52/2.00  num_eq_ax_congr_red:                    15
% 11.52/2.00  num_of_sem_filtered_clauses:            1
% 11.52/2.00  num_of_subtypes:                        0
% 11.52/2.00  monotx_restored_types:                  0
% 11.52/2.00  sat_num_of_epr_types:                   0
% 11.52/2.00  sat_num_of_non_cyclic_types:            0
% 11.52/2.00  sat_guarded_non_collapsed_types:        0
% 11.52/2.00  num_pure_diseq_elim:                    0
% 11.52/2.00  simp_replaced_by:                       0
% 11.52/2.00  res_preprocessed:                       164
% 11.52/2.00  prep_upred:                             0
% 11.52/2.00  prep_unflattend:                        44
% 11.52/2.00  smt_new_axioms:                         0
% 11.52/2.00  pred_elim_cands:                        4
% 11.52/2.00  pred_elim:                              4
% 11.52/2.00  pred_elim_cl:                           5
% 11.52/2.00  pred_elim_cycles:                       6
% 11.52/2.00  merged_defs:                            0
% 11.52/2.00  merged_defs_ncl:                        0
% 11.52/2.00  bin_hyper_res:                          0
% 11.52/2.00  prep_cycles:                            4
% 11.52/2.00  pred_elim_time:                         0.007
% 11.52/2.00  splitting_time:                         0.
% 11.52/2.00  sem_filter_time:                        0.
% 11.52/2.00  monotx_time:                            0.
% 11.52/2.00  subtype_inf_time:                       0.
% 11.52/2.00  
% 11.52/2.00  ------ Problem properties
% 11.52/2.00  
% 11.52/2.00  clauses:                                33
% 11.52/2.00  conjectures:                            4
% 11.52/2.00  epr:                                    4
% 11.52/2.00  horn:                                   31
% 11.52/2.00  ground:                                 12
% 11.52/2.00  unary:                                  9
% 11.52/2.00  binary:                                 9
% 11.52/2.00  lits:                                   84
% 11.52/2.00  lits_eq:                                31
% 11.52/2.00  fd_pure:                                0
% 11.52/2.00  fd_pseudo:                              0
% 11.52/2.00  fd_cond:                                3
% 11.52/2.00  fd_pseudo_cond:                         0
% 11.52/2.00  ac_symbols:                             0
% 11.52/2.00  
% 11.52/2.00  ------ Propositional Solver
% 11.52/2.00  
% 11.52/2.00  prop_solver_calls:                      37
% 11.52/2.00  prop_fast_solver_calls:                 2072
% 11.52/2.00  smt_solver_calls:                       0
% 11.52/2.00  smt_fast_solver_calls:                  0
% 11.52/2.00  prop_num_of_clauses:                    12047
% 11.52/2.00  prop_preprocess_simplified:             23278
% 11.52/2.00  prop_fo_subsumed:                       107
% 11.52/2.00  prop_solver_time:                       0.
% 11.52/2.00  smt_solver_time:                        0.
% 11.52/2.00  smt_fast_solver_time:                   0.
% 11.52/2.00  prop_fast_solver_time:                  0.
% 11.52/2.00  prop_unsat_core_time:                   0.001
% 11.52/2.00  
% 11.52/2.00  ------ QBF
% 11.52/2.00  
% 11.52/2.00  qbf_q_res:                              0
% 11.52/2.00  qbf_num_tautologies:                    0
% 11.52/2.00  qbf_prep_cycles:                        0
% 11.52/2.00  
% 11.52/2.00  ------ BMC1
% 11.52/2.00  
% 11.52/2.00  bmc1_current_bound:                     -1
% 11.52/2.00  bmc1_last_solved_bound:                 -1
% 11.52/2.00  bmc1_unsat_core_size:                   -1
% 11.52/2.00  bmc1_unsat_core_parents_size:           -1
% 11.52/2.00  bmc1_merge_next_fun:                    0
% 11.52/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.52/2.00  
% 11.52/2.00  ------ Instantiation
% 11.52/2.00  
% 11.52/2.00  inst_num_of_clauses:                    5944
% 11.52/2.00  inst_num_in_passive:                    2127
% 11.52/2.00  inst_num_in_active:                     2135
% 11.52/2.00  inst_num_in_unprocessed:                1682
% 11.52/2.00  inst_num_of_loops:                      2200
% 11.52/2.00  inst_num_of_learning_restarts:          0
% 11.52/2.00  inst_num_moves_active_passive:          60
% 11.52/2.00  inst_lit_activity:                      0
% 11.52/2.00  inst_lit_activity_moves:                0
% 11.52/2.00  inst_num_tautologies:                   0
% 11.52/2.00  inst_num_prop_implied:                  0
% 11.52/2.00  inst_num_existing_simplified:           0
% 11.52/2.00  inst_num_eq_res_simplified:             0
% 11.52/2.00  inst_num_child_elim:                    0
% 11.52/2.00  inst_num_of_dismatching_blockings:      1148
% 11.52/2.00  inst_num_of_non_proper_insts:           4978
% 11.52/2.00  inst_num_of_duplicates:                 0
% 11.52/2.00  inst_inst_num_from_inst_to_res:         0
% 11.52/2.00  inst_dismatching_checking_time:         0.
% 11.52/2.00  
% 11.52/2.00  ------ Resolution
% 11.52/2.00  
% 11.52/2.00  res_num_of_clauses:                     0
% 11.52/2.00  res_num_in_passive:                     0
% 11.52/2.00  res_num_in_active:                      0
% 11.52/2.00  res_num_of_loops:                       168
% 11.52/2.00  res_forward_subset_subsumed:            211
% 11.52/2.00  res_backward_subset_subsumed:           0
% 11.52/2.00  res_forward_subsumed:                   0
% 11.52/2.00  res_backward_subsumed:                  0
% 11.52/2.00  res_forward_subsumption_resolution:     1
% 11.52/2.00  res_backward_subsumption_resolution:    0
% 11.52/2.00  res_clause_to_clause_subsumption:       3483
% 11.52/2.00  res_orphan_elimination:                 0
% 11.52/2.00  res_tautology_del:                      170
% 11.52/2.00  res_num_eq_res_simplified:              0
% 11.52/2.00  res_num_sel_changes:                    0
% 11.52/2.00  res_moves_from_active_to_pass:          0
% 11.52/2.00  
% 11.52/2.00  ------ Superposition
% 11.52/2.00  
% 11.52/2.00  sup_time_total:                         0.
% 11.52/2.00  sup_time_generating:                    0.
% 11.52/2.00  sup_time_sim_full:                      0.
% 11.52/2.00  sup_time_sim_immed:                     0.
% 11.52/2.00  
% 11.52/2.00  sup_num_of_clauses:                     1066
% 11.52/2.00  sup_num_in_active:                      329
% 11.52/2.00  sup_num_in_passive:                     737
% 11.52/2.00  sup_num_of_loops:                       438
% 11.52/2.00  sup_fw_superposition:                   1338
% 11.52/2.00  sup_bw_superposition:                   671
% 11.52/2.00  sup_immediate_simplified:               777
% 11.52/2.00  sup_given_eliminated:                   4
% 11.52/2.00  comparisons_done:                       0
% 11.52/2.00  comparisons_avoided:                    0
% 11.52/2.00  
% 11.52/2.00  ------ Simplifications
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  sim_fw_subset_subsumed:                 72
% 11.52/2.00  sim_bw_subset_subsumed:                 98
% 11.52/2.00  sim_fw_subsumed:                        65
% 11.52/2.00  sim_bw_subsumed:                        48
% 11.52/2.00  sim_fw_subsumption_res:                 0
% 11.52/2.00  sim_bw_subsumption_res:                 0
% 11.52/2.00  sim_tautology_del:                      14
% 11.52/2.00  sim_eq_tautology_del:                   192
% 11.52/2.00  sim_eq_res_simp:                        2
% 11.52/2.00  sim_fw_demodulated:                     270
% 11.52/2.00  sim_bw_demodulated:                     53
% 11.52/2.00  sim_light_normalised:                   411
% 11.52/2.00  sim_joinable_taut:                      0
% 11.52/2.00  sim_joinable_simp:                      0
% 11.52/2.00  sim_ac_normalised:                      0
% 11.52/2.00  sim_smt_subsumption:                    0
% 11.52/2.00  
%------------------------------------------------------------------------------
