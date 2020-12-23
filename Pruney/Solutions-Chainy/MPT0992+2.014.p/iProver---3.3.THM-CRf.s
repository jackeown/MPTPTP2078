%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:49 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  190 (2608 expanded)
%              Number of clauses        :  125 ( 888 expanded)
%              Number of leaves         :   20 ( 492 expanded)
%              Depth                    :   26
%              Number of atoms          :  543 (13832 expanded)
%              Number of equality atoms :  258 (3547 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46])).

fof(f79,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2345,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_831,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_833,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_31])).

cnf(c_2344,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2350,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3356,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2344,c_2350])).

cnf(c_3512,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_833,c_3356])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2354,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3921,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3512,c_2354])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2619,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2620,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_4343,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3921,c_36,c_2620])).

cnf(c_4344,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4343])).

cnf(c_4353,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2345,c_4344])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2346,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4874,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_2346])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2347,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4719,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2347])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2703,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2784,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_5075,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4719,c_33,c_31,c_2784])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4053,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2348])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2672,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2779,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_2780,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2779])).

cnf(c_4214,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4053,c_34,c_36,c_2780])).

cnf(c_5084,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5075,c_4214])).

cnf(c_5456,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4874,c_5084])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_841,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_842,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_363,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_11])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_854,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_842,c_11,c_364])).

cnf(c_2332,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_858,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_2838,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_2839,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2838])).

cnf(c_2967,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2332,c_34,c_36,c_858,c_2839])).

cnf(c_2968,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2967])).

cnf(c_5080,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5075,c_2968])).

cnf(c_5155,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_5080])).

cnf(c_5468,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5456,c_5155])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2349,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5133,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_2349])).

cnf(c_5269,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5133,c_34,c_36])).

cnf(c_2352,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5284,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_2352])).

cnf(c_2341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_5281,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_2341])).

cnf(c_6063,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5468,c_5284,c_5281])).

cnf(c_6069,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6063,c_5080])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6080,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6063,c_29])).

cnf(c_6081,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6080])).

cnf(c_6343,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6081,c_2345])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3920,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2354])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2355,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_6])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_13,c_11,c_6])).

cnf(c_2342,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_3291,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2355,c_2342])).

cnf(c_3933,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3920,c_8,c_3291])).

cnf(c_2611,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2613,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2611])).

cnf(c_2612,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2612])).

cnf(c_3947,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3933,c_2613,c_2615])).

cnf(c_3948,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3947])).

cnf(c_6372,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6343,c_3948])).

cnf(c_3292,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(superposition,[status(thm)],[c_2344,c_2342])).

cnf(c_6342,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_6081,c_3292])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2358,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5282,plain,
    ( v1_xboole_0(k7_relat_1(sK3,X0)) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_2351])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2356,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5844,plain,
    ( k7_relat_1(sK3,X0) = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5282,c_2356])).

cnf(c_103,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_108,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1857,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2807,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_2808,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2807])).

cnf(c_2810,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2808])).

cnf(c_1856,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2659,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_2899,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_1855,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2900,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_3421,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_3422,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3421])).

cnf(c_6831,plain,
    ( v1_xboole_0(X1) != iProver_top
    | k7_relat_1(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5844,c_29,c_103,c_0,c_108,c_2810,c_2899,c_2900,c_3422,c_6063])).

cnf(c_6832,plain,
    ( k7_relat_1(sK3,X0) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6831])).

cnf(c_6839,plain,
    ( k7_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2358,c_6832])).

cnf(c_7198,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6342,c_6839])).

cnf(c_7900,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6069,c_6372,c_7198])).

cnf(c_7901,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7900,c_8,c_3291])).

cnf(c_7902,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7901])).

cnf(c_7904,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7902,c_2355])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:59:51 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.19/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.96  
% 3.19/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.96  
% 3.19/0.96  ------  iProver source info
% 3.19/0.96  
% 3.19/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.96  git: non_committed_changes: false
% 3.19/0.96  git: last_make_outside_of_git: false
% 3.19/0.96  
% 3.19/0.96  ------ 
% 3.19/0.96  
% 3.19/0.96  ------ Input Options
% 3.19/0.96  
% 3.19/0.96  --out_options                           all
% 3.19/0.96  --tptp_safe_out                         true
% 3.19/0.96  --problem_path                          ""
% 3.19/0.96  --include_path                          ""
% 3.19/0.96  --clausifier                            res/vclausify_rel
% 3.19/0.96  --clausifier_options                    --mode clausify
% 3.19/0.96  --stdin                                 false
% 3.19/0.96  --stats_out                             all
% 3.19/0.96  
% 3.19/0.96  ------ General Options
% 3.19/0.96  
% 3.19/0.96  --fof                                   false
% 3.19/0.96  --time_out_real                         305.
% 3.19/0.96  --time_out_virtual                      -1.
% 3.19/0.96  --symbol_type_check                     false
% 3.19/0.96  --clausify_out                          false
% 3.19/0.96  --sig_cnt_out                           false
% 3.19/0.96  --trig_cnt_out                          false
% 3.19/0.96  --trig_cnt_out_tolerance                1.
% 3.19/0.96  --trig_cnt_out_sk_spl                   false
% 3.19/0.96  --abstr_cl_out                          false
% 3.19/0.96  
% 3.19/0.96  ------ Global Options
% 3.19/0.96  
% 3.19/0.96  --schedule                              default
% 3.19/0.96  --add_important_lit                     false
% 3.19/0.96  --prop_solver_per_cl                    1000
% 3.19/0.96  --min_unsat_core                        false
% 3.19/0.96  --soft_assumptions                      false
% 3.19/0.96  --soft_lemma_size                       3
% 3.19/0.96  --prop_impl_unit_size                   0
% 3.19/0.96  --prop_impl_unit                        []
% 3.19/0.96  --share_sel_clauses                     true
% 3.19/0.96  --reset_solvers                         false
% 3.19/0.96  --bc_imp_inh                            [conj_cone]
% 3.19/0.96  --conj_cone_tolerance                   3.
% 3.19/0.96  --extra_neg_conj                        none
% 3.19/0.96  --large_theory_mode                     true
% 3.19/0.96  --prolific_symb_bound                   200
% 3.19/0.96  --lt_threshold                          2000
% 3.19/0.96  --clause_weak_htbl                      true
% 3.19/0.96  --gc_record_bc_elim                     false
% 3.19/0.96  
% 3.19/0.96  ------ Preprocessing Options
% 3.19/0.96  
% 3.19/0.96  --preprocessing_flag                    true
% 3.19/0.96  --time_out_prep_mult                    0.1
% 3.19/0.96  --splitting_mode                        input
% 3.19/0.96  --splitting_grd                         true
% 3.19/0.96  --splitting_cvd                         false
% 3.19/0.96  --splitting_cvd_svl                     false
% 3.19/0.96  --splitting_nvd                         32
% 3.19/0.96  --sub_typing                            true
% 3.19/0.96  --prep_gs_sim                           true
% 3.19/0.96  --prep_unflatten                        true
% 3.19/0.96  --prep_res_sim                          true
% 3.19/0.96  --prep_upred                            true
% 3.19/0.96  --prep_sem_filter                       exhaustive
% 3.19/0.96  --prep_sem_filter_out                   false
% 3.19/0.96  --pred_elim                             true
% 3.19/0.96  --res_sim_input                         true
% 3.19/0.96  --eq_ax_congr_red                       true
% 3.19/0.96  --pure_diseq_elim                       true
% 3.19/0.96  --brand_transform                       false
% 3.19/0.96  --non_eq_to_eq                          false
% 3.19/0.96  --prep_def_merge                        true
% 3.19/0.96  --prep_def_merge_prop_impl              false
% 3.19/0.96  --prep_def_merge_mbd                    true
% 3.19/0.96  --prep_def_merge_tr_red                 false
% 3.19/0.96  --prep_def_merge_tr_cl                  false
% 3.19/0.96  --smt_preprocessing                     true
% 3.19/0.96  --smt_ac_axioms                         fast
% 3.19/0.96  --preprocessed_out                      false
% 3.19/0.96  --preprocessed_stats                    false
% 3.19/0.96  
% 3.19/0.96  ------ Abstraction refinement Options
% 3.19/0.96  
% 3.19/0.96  --abstr_ref                             []
% 3.19/0.96  --abstr_ref_prep                        false
% 3.19/0.96  --abstr_ref_until_sat                   false
% 3.19/0.96  --abstr_ref_sig_restrict                funpre
% 3.19/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.96  --abstr_ref_under                       []
% 3.19/0.96  
% 3.19/0.96  ------ SAT Options
% 3.19/0.96  
% 3.19/0.96  --sat_mode                              false
% 3.19/0.96  --sat_fm_restart_options                ""
% 3.19/0.96  --sat_gr_def                            false
% 3.19/0.96  --sat_epr_types                         true
% 3.19/0.96  --sat_non_cyclic_types                  false
% 3.19/0.96  --sat_finite_models                     false
% 3.19/0.96  --sat_fm_lemmas                         false
% 3.19/0.96  --sat_fm_prep                           false
% 3.19/0.96  --sat_fm_uc_incr                        true
% 3.19/0.96  --sat_out_model                         small
% 3.19/0.96  --sat_out_clauses                       false
% 3.19/0.96  
% 3.19/0.96  ------ QBF Options
% 3.19/0.96  
% 3.19/0.96  --qbf_mode                              false
% 3.19/0.96  --qbf_elim_univ                         false
% 3.19/0.96  --qbf_dom_inst                          none
% 3.19/0.96  --qbf_dom_pre_inst                      false
% 3.19/0.96  --qbf_sk_in                             false
% 3.19/0.96  --qbf_pred_elim                         true
% 3.19/0.96  --qbf_split                             512
% 3.19/0.96  
% 3.19/0.96  ------ BMC1 Options
% 3.19/0.96  
% 3.19/0.96  --bmc1_incremental                      false
% 3.19/0.96  --bmc1_axioms                           reachable_all
% 3.19/0.96  --bmc1_min_bound                        0
% 3.19/0.96  --bmc1_max_bound                        -1
% 3.19/0.96  --bmc1_max_bound_default                -1
% 3.19/0.96  --bmc1_symbol_reachability              true
% 3.19/0.96  --bmc1_property_lemmas                  false
% 3.19/0.96  --bmc1_k_induction                      false
% 3.19/0.96  --bmc1_non_equiv_states                 false
% 3.19/0.96  --bmc1_deadlock                         false
% 3.19/0.96  --bmc1_ucm                              false
% 3.19/0.96  --bmc1_add_unsat_core                   none
% 3.19/0.96  --bmc1_unsat_core_children              false
% 3.19/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.96  --bmc1_out_stat                         full
% 3.19/0.96  --bmc1_ground_init                      false
% 3.19/0.96  --bmc1_pre_inst_next_state              false
% 3.19/0.96  --bmc1_pre_inst_state                   false
% 3.19/0.96  --bmc1_pre_inst_reach_state             false
% 3.19/0.96  --bmc1_out_unsat_core                   false
% 3.19/0.96  --bmc1_aig_witness_out                  false
% 3.19/0.96  --bmc1_verbose                          false
% 3.19/0.96  --bmc1_dump_clauses_tptp                false
% 3.19/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.96  --bmc1_dump_file                        -
% 3.19/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.96  --bmc1_ucm_extend_mode                  1
% 3.19/0.96  --bmc1_ucm_init_mode                    2
% 3.19/0.96  --bmc1_ucm_cone_mode                    none
% 3.19/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.96  --bmc1_ucm_relax_model                  4
% 3.19/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.96  --bmc1_ucm_layered_model                none
% 3.19/0.96  --bmc1_ucm_max_lemma_size               10
% 3.19/0.96  
% 3.19/0.96  ------ AIG Options
% 3.19/0.96  
% 3.19/0.96  --aig_mode                              false
% 3.19/0.96  
% 3.19/0.96  ------ Instantiation Options
% 3.19/0.96  
% 3.19/0.96  --instantiation_flag                    true
% 3.19/0.96  --inst_sos_flag                         false
% 3.19/0.96  --inst_sos_phase                        true
% 3.19/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.96  --inst_lit_sel_side                     num_symb
% 3.19/0.96  --inst_solver_per_active                1400
% 3.19/0.96  --inst_solver_calls_frac                1.
% 3.19/0.96  --inst_passive_queue_type               priority_queues
% 3.19/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.96  --inst_passive_queues_freq              [25;2]
% 3.19/0.96  --inst_dismatching                      true
% 3.19/0.96  --inst_eager_unprocessed_to_passive     true
% 3.19/0.96  --inst_prop_sim_given                   true
% 3.19/0.96  --inst_prop_sim_new                     false
% 3.19/0.96  --inst_subs_new                         false
% 3.19/0.96  --inst_eq_res_simp                      false
% 3.19/0.96  --inst_subs_given                       false
% 3.19/0.96  --inst_orphan_elimination               true
% 3.19/0.96  --inst_learning_loop_flag               true
% 3.19/0.96  --inst_learning_start                   3000
% 3.19/0.96  --inst_learning_factor                  2
% 3.19/0.96  --inst_start_prop_sim_after_learn       3
% 3.19/0.96  --inst_sel_renew                        solver
% 3.19/0.96  --inst_lit_activity_flag                true
% 3.19/0.96  --inst_restr_to_given                   false
% 3.19/0.96  --inst_activity_threshold               500
% 3.19/0.96  --inst_out_proof                        true
% 3.19/0.96  
% 3.19/0.96  ------ Resolution Options
% 3.19/0.96  
% 3.19/0.96  --resolution_flag                       true
% 3.19/0.96  --res_lit_sel                           adaptive
% 3.19/0.96  --res_lit_sel_side                      none
% 3.19/0.96  --res_ordering                          kbo
% 3.19/0.96  --res_to_prop_solver                    active
% 3.19/0.96  --res_prop_simpl_new                    false
% 3.19/0.96  --res_prop_simpl_given                  true
% 3.19/0.96  --res_passive_queue_type                priority_queues
% 3.19/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.96  --res_passive_queues_freq               [15;5]
% 3.19/0.96  --res_forward_subs                      full
% 3.19/0.96  --res_backward_subs                     full
% 3.19/0.96  --res_forward_subs_resolution           true
% 3.19/0.96  --res_backward_subs_resolution          true
% 3.19/0.96  --res_orphan_elimination                true
% 3.19/0.96  --res_time_limit                        2.
% 3.19/0.96  --res_out_proof                         true
% 3.19/0.96  
% 3.19/0.96  ------ Superposition Options
% 3.19/0.96  
% 3.19/0.96  --superposition_flag                    true
% 3.19/0.96  --sup_passive_queue_type                priority_queues
% 3.19/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.96  --demod_completeness_check              fast
% 3.19/0.96  --demod_use_ground                      true
% 3.19/0.96  --sup_to_prop_solver                    passive
% 3.19/0.96  --sup_prop_simpl_new                    true
% 3.19/0.96  --sup_prop_simpl_given                  true
% 3.19/0.96  --sup_fun_splitting                     false
% 3.19/0.96  --sup_smt_interval                      50000
% 3.19/0.96  
% 3.19/0.96  ------ Superposition Simplification Setup
% 3.19/0.96  
% 3.19/0.96  --sup_indices_passive                   []
% 3.19/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.96  --sup_full_bw                           [BwDemod]
% 3.19/0.96  --sup_immed_triv                        [TrivRules]
% 3.19/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.96  --sup_immed_bw_main                     []
% 3.19/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.96  
% 3.19/0.96  ------ Combination Options
% 3.19/0.96  
% 3.19/0.96  --comb_res_mult                         3
% 3.19/0.96  --comb_sup_mult                         2
% 3.19/0.96  --comb_inst_mult                        10
% 3.19/0.96  
% 3.19/0.96  ------ Debug Options
% 3.19/0.96  
% 3.19/0.96  --dbg_backtrace                         false
% 3.19/0.96  --dbg_dump_prop_clauses                 false
% 3.19/0.96  --dbg_dump_prop_clauses_file            -
% 3.19/0.96  --dbg_out_stat                          false
% 3.19/0.96  ------ Parsing...
% 3.19/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.96  
% 3.19/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.19/0.96  
% 3.19/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.96  
% 3.19/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.96  ------ Proving...
% 3.19/0.96  ------ Problem Properties 
% 3.19/0.96  
% 3.19/0.96  
% 3.19/0.96  clauses                                 32
% 3.19/0.96  conjectures                             4
% 3.19/0.96  EPR                                     6
% 3.19/0.96  Horn                                    28
% 3.19/0.96  unary                                   8
% 3.19/0.96  binary                                  6
% 3.19/0.96  lits                                    88
% 3.19/0.96  lits eq                                 32
% 3.19/0.96  fd_pure                                 0
% 3.19/0.96  fd_pseudo                               0
% 3.19/0.96  fd_cond                                 2
% 3.19/0.96  fd_pseudo_cond                          1
% 3.19/0.96  AC symbols                              0
% 3.19/0.96  
% 3.19/0.96  ------ Schedule dynamic 5 is on 
% 3.19/0.96  
% 3.19/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.96  
% 3.19/0.96  
% 3.19/0.96  ------ 
% 3.19/0.96  Current options:
% 3.19/0.96  ------ 
% 3.19/0.96  
% 3.19/0.96  ------ Input Options
% 3.19/0.96  
% 3.19/0.96  --out_options                           all
% 3.19/0.96  --tptp_safe_out                         true
% 3.19/0.96  --problem_path                          ""
% 3.19/0.96  --include_path                          ""
% 3.19/0.96  --clausifier                            res/vclausify_rel
% 3.19/0.96  --clausifier_options                    --mode clausify
% 3.19/0.96  --stdin                                 false
% 3.19/0.96  --stats_out                             all
% 3.19/0.96  
% 3.19/0.96  ------ General Options
% 3.19/0.96  
% 3.19/0.96  --fof                                   false
% 3.19/0.96  --time_out_real                         305.
% 3.19/0.96  --time_out_virtual                      -1.
% 3.19/0.96  --symbol_type_check                     false
% 3.19/0.96  --clausify_out                          false
% 3.19/0.96  --sig_cnt_out                           false
% 3.19/0.96  --trig_cnt_out                          false
% 3.19/0.96  --trig_cnt_out_tolerance                1.
% 3.19/0.96  --trig_cnt_out_sk_spl                   false
% 3.19/0.96  --abstr_cl_out                          false
% 3.19/0.96  
% 3.19/0.96  ------ Global Options
% 3.19/0.96  
% 3.19/0.96  --schedule                              default
% 3.19/0.96  --add_important_lit                     false
% 3.19/0.96  --prop_solver_per_cl                    1000
% 3.19/0.96  --min_unsat_core                        false
% 3.19/0.96  --soft_assumptions                      false
% 3.19/0.96  --soft_lemma_size                       3
% 3.19/0.96  --prop_impl_unit_size                   0
% 3.19/0.96  --prop_impl_unit                        []
% 3.19/0.96  --share_sel_clauses                     true
% 3.19/0.96  --reset_solvers                         false
% 3.19/0.96  --bc_imp_inh                            [conj_cone]
% 3.19/0.96  --conj_cone_tolerance                   3.
% 3.19/0.96  --extra_neg_conj                        none
% 3.19/0.96  --large_theory_mode                     true
% 3.19/0.96  --prolific_symb_bound                   200
% 3.19/0.96  --lt_threshold                          2000
% 3.19/0.96  --clause_weak_htbl                      true
% 3.19/0.96  --gc_record_bc_elim                     false
% 3.19/0.96  
% 3.19/0.96  ------ Preprocessing Options
% 3.19/0.96  
% 3.19/0.96  --preprocessing_flag                    true
% 3.19/0.96  --time_out_prep_mult                    0.1
% 3.19/0.96  --splitting_mode                        input
% 3.19/0.96  --splitting_grd                         true
% 3.19/0.96  --splitting_cvd                         false
% 3.19/0.96  --splitting_cvd_svl                     false
% 3.19/0.96  --splitting_nvd                         32
% 3.19/0.96  --sub_typing                            true
% 3.19/0.96  --prep_gs_sim                           true
% 3.19/0.96  --prep_unflatten                        true
% 3.19/0.96  --prep_res_sim                          true
% 3.19/0.96  --prep_upred                            true
% 3.19/0.96  --prep_sem_filter                       exhaustive
% 3.19/0.96  --prep_sem_filter_out                   false
% 3.19/0.96  --pred_elim                             true
% 3.19/0.96  --res_sim_input                         true
% 3.19/0.96  --eq_ax_congr_red                       true
% 3.19/0.96  --pure_diseq_elim                       true
% 3.19/0.96  --brand_transform                       false
% 3.19/0.96  --non_eq_to_eq                          false
% 3.19/0.96  --prep_def_merge                        true
% 3.19/0.96  --prep_def_merge_prop_impl              false
% 3.19/0.96  --prep_def_merge_mbd                    true
% 3.19/0.96  --prep_def_merge_tr_red                 false
% 3.19/0.96  --prep_def_merge_tr_cl                  false
% 3.19/0.96  --smt_preprocessing                     true
% 3.19/0.96  --smt_ac_axioms                         fast
% 3.19/0.96  --preprocessed_out                      false
% 3.19/0.96  --preprocessed_stats                    false
% 3.19/0.96  
% 3.19/0.96  ------ Abstraction refinement Options
% 3.19/0.96  
% 3.19/0.96  --abstr_ref                             []
% 3.19/0.96  --abstr_ref_prep                        false
% 3.19/0.96  --abstr_ref_until_sat                   false
% 3.19/0.96  --abstr_ref_sig_restrict                funpre
% 3.19/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.96  --abstr_ref_under                       []
% 3.19/0.96  
% 3.19/0.96  ------ SAT Options
% 3.19/0.96  
% 3.19/0.96  --sat_mode                              false
% 3.19/0.96  --sat_fm_restart_options                ""
% 3.19/0.96  --sat_gr_def                            false
% 3.19/0.96  --sat_epr_types                         true
% 3.19/0.96  --sat_non_cyclic_types                  false
% 3.19/0.96  --sat_finite_models                     false
% 3.19/0.96  --sat_fm_lemmas                         false
% 3.19/0.96  --sat_fm_prep                           false
% 3.19/0.96  --sat_fm_uc_incr                        true
% 3.19/0.96  --sat_out_model                         small
% 3.19/0.96  --sat_out_clauses                       false
% 3.19/0.96  
% 3.19/0.96  ------ QBF Options
% 3.19/0.96  
% 3.19/0.96  --qbf_mode                              false
% 3.19/0.96  --qbf_elim_univ                         false
% 3.19/0.96  --qbf_dom_inst                          none
% 3.19/0.96  --qbf_dom_pre_inst                      false
% 3.19/0.96  --qbf_sk_in                             false
% 3.19/0.96  --qbf_pred_elim                         true
% 3.19/0.96  --qbf_split                             512
% 3.19/0.96  
% 3.19/0.96  ------ BMC1 Options
% 3.19/0.96  
% 3.19/0.96  --bmc1_incremental                      false
% 3.19/0.96  --bmc1_axioms                           reachable_all
% 3.19/0.96  --bmc1_min_bound                        0
% 3.19/0.96  --bmc1_max_bound                        -1
% 3.19/0.96  --bmc1_max_bound_default                -1
% 3.19/0.96  --bmc1_symbol_reachability              true
% 3.19/0.96  --bmc1_property_lemmas                  false
% 3.19/0.96  --bmc1_k_induction                      false
% 3.19/0.96  --bmc1_non_equiv_states                 false
% 3.19/0.96  --bmc1_deadlock                         false
% 3.19/0.96  --bmc1_ucm                              false
% 3.19/0.96  --bmc1_add_unsat_core                   none
% 3.19/0.96  --bmc1_unsat_core_children              false
% 3.19/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.96  --bmc1_out_stat                         full
% 3.19/0.96  --bmc1_ground_init                      false
% 3.19/0.96  --bmc1_pre_inst_next_state              false
% 3.19/0.96  --bmc1_pre_inst_state                   false
% 3.19/0.96  --bmc1_pre_inst_reach_state             false
% 3.19/0.96  --bmc1_out_unsat_core                   false
% 3.19/0.96  --bmc1_aig_witness_out                  false
% 3.19/0.96  --bmc1_verbose                          false
% 3.19/0.96  --bmc1_dump_clauses_tptp                false
% 3.19/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.96  --bmc1_dump_file                        -
% 3.19/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.96  --bmc1_ucm_extend_mode                  1
% 3.19/0.96  --bmc1_ucm_init_mode                    2
% 3.19/0.96  --bmc1_ucm_cone_mode                    none
% 3.19/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.96  --bmc1_ucm_relax_model                  4
% 3.19/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.96  --bmc1_ucm_layered_model                none
% 3.19/0.96  --bmc1_ucm_max_lemma_size               10
% 3.19/0.96  
% 3.19/0.96  ------ AIG Options
% 3.19/0.96  
% 3.19/0.96  --aig_mode                              false
% 3.19/0.96  
% 3.19/0.96  ------ Instantiation Options
% 3.19/0.96  
% 3.19/0.96  --instantiation_flag                    true
% 3.19/0.96  --inst_sos_flag                         false
% 3.19/0.96  --inst_sos_phase                        true
% 3.19/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.96  --inst_lit_sel_side                     none
% 3.19/0.96  --inst_solver_per_active                1400
% 3.19/0.96  --inst_solver_calls_frac                1.
% 3.19/0.96  --inst_passive_queue_type               priority_queues
% 3.19/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.96  --inst_passive_queues_freq              [25;2]
% 3.19/0.96  --inst_dismatching                      true
% 3.19/0.96  --inst_eager_unprocessed_to_passive     true
% 3.19/0.96  --inst_prop_sim_given                   true
% 3.19/0.96  --inst_prop_sim_new                     false
% 3.19/0.96  --inst_subs_new                         false
% 3.19/0.96  --inst_eq_res_simp                      false
% 3.19/0.96  --inst_subs_given                       false
% 3.19/0.96  --inst_orphan_elimination               true
% 3.19/0.96  --inst_learning_loop_flag               true
% 3.19/0.96  --inst_learning_start                   3000
% 3.19/0.96  --inst_learning_factor                  2
% 3.19/0.96  --inst_start_prop_sim_after_learn       3
% 3.19/0.96  --inst_sel_renew                        solver
% 3.19/0.96  --inst_lit_activity_flag                true
% 3.19/0.96  --inst_restr_to_given                   false
% 3.19/0.96  --inst_activity_threshold               500
% 3.19/0.96  --inst_out_proof                        true
% 3.19/0.96  
% 3.19/0.96  ------ Resolution Options
% 3.19/0.96  
% 3.19/0.96  --resolution_flag                       false
% 3.19/0.96  --res_lit_sel                           adaptive
% 3.19/0.96  --res_lit_sel_side                      none
% 3.19/0.96  --res_ordering                          kbo
% 3.19/0.96  --res_to_prop_solver                    active
% 3.19/0.96  --res_prop_simpl_new                    false
% 3.19/0.96  --res_prop_simpl_given                  true
% 3.19/0.96  --res_passive_queue_type                priority_queues
% 3.19/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.96  --res_passive_queues_freq               [15;5]
% 3.19/0.96  --res_forward_subs                      full
% 3.19/0.96  --res_backward_subs                     full
% 3.19/0.96  --res_forward_subs_resolution           true
% 3.19/0.96  --res_backward_subs_resolution          true
% 3.19/0.96  --res_orphan_elimination                true
% 3.19/0.96  --res_time_limit                        2.
% 3.19/0.96  --res_out_proof                         true
% 3.19/0.96  
% 3.19/0.96  ------ Superposition Options
% 3.19/0.96  
% 3.19/0.96  --superposition_flag                    true
% 3.19/0.96  --sup_passive_queue_type                priority_queues
% 3.19/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.96  --demod_completeness_check              fast
% 3.19/0.96  --demod_use_ground                      true
% 3.19/0.96  --sup_to_prop_solver                    passive
% 3.19/0.96  --sup_prop_simpl_new                    true
% 3.19/0.96  --sup_prop_simpl_given                  true
% 3.19/0.96  --sup_fun_splitting                     false
% 3.19/0.96  --sup_smt_interval                      50000
% 3.19/0.96  
% 3.19/0.96  ------ Superposition Simplification Setup
% 3.19/0.96  
% 3.19/0.96  --sup_indices_passive                   []
% 3.19/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.96  --sup_full_bw                           [BwDemod]
% 3.19/0.96  --sup_immed_triv                        [TrivRules]
% 3.19/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.97  --sup_immed_bw_main                     []
% 3.19/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.97  
% 3.19/0.97  ------ Combination Options
% 3.19/0.97  
% 3.19/0.97  --comb_res_mult                         3
% 3.19/0.97  --comb_sup_mult                         2
% 3.19/0.97  --comb_inst_mult                        10
% 3.19/0.97  
% 3.19/0.97  ------ Debug Options
% 3.19/0.97  
% 3.19/0.97  --dbg_backtrace                         false
% 3.19/0.97  --dbg_dump_prop_clauses                 false
% 3.19/0.97  --dbg_dump_prop_clauses_file            -
% 3.19/0.97  --dbg_out_stat                          false
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  ------ Proving...
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  % SZS status Theorem for theBenchmark.p
% 3.19/0.97  
% 3.19/0.97   Resolution empty clause
% 3.19/0.97  
% 3.19/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.97  
% 3.19/0.97  fof(f19,conjecture,(
% 3.19/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f20,negated_conjecture,(
% 3.19/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.19/0.97    inference(negated_conjecture,[],[f19])).
% 3.19/0.97  
% 3.19/0.97  fof(f42,plain,(
% 3.19/0.97    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.19/0.97    inference(ennf_transformation,[],[f20])).
% 3.19/0.97  
% 3.19/0.97  fof(f43,plain,(
% 3.19/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.19/0.97    inference(flattening,[],[f42])).
% 3.19/0.97  
% 3.19/0.97  fof(f46,plain,(
% 3.19/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.19/0.97    introduced(choice_axiom,[])).
% 3.19/0.97  
% 3.19/0.97  fof(f47,plain,(
% 3.19/0.97    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.19/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46])).
% 3.19/0.97  
% 3.19/0.97  fof(f79,plain,(
% 3.19/0.97    r1_tarski(sK2,sK0)),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f15,axiom,(
% 3.19/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f34,plain,(
% 3.19/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(ennf_transformation,[],[f15])).
% 3.19/0.97  
% 3.19/0.97  fof(f35,plain,(
% 3.19/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(flattening,[],[f34])).
% 3.19/0.97  
% 3.19/0.97  fof(f45,plain,(
% 3.19/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(nnf_transformation,[],[f35])).
% 3.19/0.97  
% 3.19/0.97  fof(f64,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f45])).
% 3.19/0.97  
% 3.19/0.97  fof(f77,plain,(
% 3.19/0.97    v1_funct_2(sK3,sK0,sK1)),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f78,plain,(
% 3.19/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f14,axiom,(
% 3.19/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f33,plain,(
% 3.19/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(ennf_transformation,[],[f14])).
% 3.19/0.97  
% 3.19/0.97  fof(f63,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f33])).
% 3.19/0.97  
% 3.19/0.97  fof(f9,axiom,(
% 3.19/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f26,plain,(
% 3.19/0.97    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(ennf_transformation,[],[f9])).
% 3.19/0.97  
% 3.19/0.97  fof(f27,plain,(
% 3.19/0.97    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(flattening,[],[f26])).
% 3.19/0.97  
% 3.19/0.97  fof(f57,plain,(
% 3.19/0.97    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f27])).
% 3.19/0.97  
% 3.19/0.97  fof(f11,axiom,(
% 3.19/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f30,plain,(
% 3.19/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(ennf_transformation,[],[f11])).
% 3.19/0.97  
% 3.19/0.97  fof(f59,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f30])).
% 3.19/0.97  
% 3.19/0.97  fof(f18,axiom,(
% 3.19/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f40,plain,(
% 3.19/0.97    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.19/0.97    inference(ennf_transformation,[],[f18])).
% 3.19/0.97  
% 3.19/0.97  fof(f41,plain,(
% 3.19/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(flattening,[],[f40])).
% 3.19/0.97  
% 3.19/0.97  fof(f75,plain,(
% 3.19/0.97    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f41])).
% 3.19/0.97  
% 3.19/0.97  fof(f17,axiom,(
% 3.19/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f38,plain,(
% 3.19/0.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.19/0.97    inference(ennf_transformation,[],[f17])).
% 3.19/0.97  
% 3.19/0.97  fof(f39,plain,(
% 3.19/0.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.19/0.97    inference(flattening,[],[f38])).
% 3.19/0.97  
% 3.19/0.97  fof(f72,plain,(
% 3.19/0.97    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f39])).
% 3.19/0.97  
% 3.19/0.97  fof(f76,plain,(
% 3.19/0.97    v1_funct_1(sK3)),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f16,axiom,(
% 3.19/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f36,plain,(
% 3.19/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.19/0.97    inference(ennf_transformation,[],[f16])).
% 3.19/0.97  
% 3.19/0.97  fof(f37,plain,(
% 3.19/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.19/0.97    inference(flattening,[],[f36])).
% 3.19/0.97  
% 3.19/0.97  fof(f70,plain,(
% 3.19/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f37])).
% 3.19/0.97  
% 3.19/0.97  fof(f74,plain,(
% 3.19/0.97    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f41])).
% 3.19/0.97  
% 3.19/0.97  fof(f81,plain,(
% 3.19/0.97    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f12,axiom,(
% 3.19/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f31,plain,(
% 3.19/0.97    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.97    inference(ennf_transformation,[],[f12])).
% 3.19/0.97  
% 3.19/0.97  fof(f61,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f31])).
% 3.19/0.97  
% 3.19/0.97  fof(f6,axiom,(
% 3.19/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f23,plain,(
% 3.19/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(ennf_transformation,[],[f6])).
% 3.19/0.97  
% 3.19/0.97  fof(f44,plain,(
% 3.19/0.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(nnf_transformation,[],[f23])).
% 3.19/0.97  
% 3.19/0.97  fof(f52,plain,(
% 3.19/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f44])).
% 3.19/0.97  
% 3.19/0.97  fof(f71,plain,(
% 3.19/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f37])).
% 3.19/0.97  
% 3.19/0.97  fof(f80,plain,(
% 3.19/0.97    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.19/0.97    inference(cnf_transformation,[],[f47])).
% 3.19/0.97  
% 3.19/0.97  fof(f8,axiom,(
% 3.19/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f55,plain,(
% 3.19/0.97    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.19/0.97    inference(cnf_transformation,[],[f8])).
% 3.19/0.97  
% 3.19/0.97  fof(f4,axiom,(
% 3.19/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f51,plain,(
% 3.19/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f4])).
% 3.19/0.97  
% 3.19/0.97  fof(f60,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.97    inference(cnf_transformation,[],[f31])).
% 3.19/0.97  
% 3.19/0.97  fof(f7,axiom,(
% 3.19/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f24,plain,(
% 3.19/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.19/0.97    inference(ennf_transformation,[],[f7])).
% 3.19/0.97  
% 3.19/0.97  fof(f25,plain,(
% 3.19/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/0.97    inference(flattening,[],[f24])).
% 3.19/0.97  
% 3.19/0.97  fof(f54,plain,(
% 3.19/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f25])).
% 3.19/0.97  
% 3.19/0.97  fof(f1,axiom,(
% 3.19/0.97    v1_xboole_0(k1_xboole_0)),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f48,plain,(
% 3.19/0.97    v1_xboole_0(k1_xboole_0)),
% 3.19/0.97    inference(cnf_transformation,[],[f1])).
% 3.19/0.97  
% 3.19/0.97  fof(f13,axiom,(
% 3.19/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f32,plain,(
% 3.19/0.97    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.19/0.97    inference(ennf_transformation,[],[f13])).
% 3.19/0.97  
% 3.19/0.97  fof(f62,plain,(
% 3.19/0.97    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f32])).
% 3.19/0.97  
% 3.19/0.97  fof(f3,axiom,(
% 3.19/0.97    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.97  
% 3.19/0.97  fof(f22,plain,(
% 3.19/0.97    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.19/0.97    inference(ennf_transformation,[],[f3])).
% 3.19/0.97  
% 3.19/0.97  fof(f50,plain,(
% 3.19/0.97    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.19/0.97    inference(cnf_transformation,[],[f22])).
% 3.19/0.97  
% 3.19/0.97  cnf(c_30,negated_conjecture,
% 3.19/0.97      ( r1_tarski(sK2,sK0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2345,plain,
% 3.19/0.97      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_21,plain,
% 3.19/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.19/0.97      | k1_xboole_0 = X2 ),
% 3.19/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_32,negated_conjecture,
% 3.19/0.97      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.19/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_830,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.19/0.97      | sK3 != X0
% 3.19/0.97      | sK1 != X2
% 3.19/0.97      | sK0 != X1
% 3.19/0.97      | k1_xboole_0 = X2 ),
% 3.19/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_831,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/0.97      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.19/0.97      | k1_xboole_0 = sK1 ),
% 3.19/0.97      inference(unflattening,[status(thm)],[c_830]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_31,negated_conjecture,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.19/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_833,plain,
% 3.19/0.97      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.19/0.97      inference(global_propositional_subsumption,[status(thm)],[c_831,c_31]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2344,plain,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_15,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2350,plain,
% 3.19/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.19/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3356,plain,
% 3.19/0.97      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2344,c_2350]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3512,plain,
% 3.19/0.97      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_833,c_3356]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_9,plain,
% 3.19/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.19/0.97      | ~ v1_relat_1(X1)
% 3.19/0.97      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.19/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2354,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.19/0.97      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.19/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3921,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.19/0.97      | sK1 = k1_xboole_0
% 3.19/0.97      | r1_tarski(X0,sK0) != iProver_top
% 3.19/0.97      | v1_relat_1(sK3) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_3512,c_2354]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_36,plain,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_11,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2619,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/0.97      | v1_relat_1(sK3) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2620,plain,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/0.97      | v1_relat_1(sK3) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4343,plain,
% 3.19/0.97      ( r1_tarski(X0,sK0) != iProver_top
% 3.19/0.97      | sK1 = k1_xboole_0
% 3.19/0.97      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_3921,c_36,c_2620]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4344,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.19/0.97      | sK1 = k1_xboole_0
% 3.19/0.97      | r1_tarski(X0,sK0) != iProver_top ),
% 3.19/0.97      inference(renaming,[status(thm)],[c_4343]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4353,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2345,c_4344]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_25,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.19/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.19/0.97      | ~ v1_funct_1(X0)
% 3.19/0.97      | ~ v1_relat_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2346,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.19/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.19/0.97      | v1_funct_1(X0) != iProver_top
% 3.19/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4874,plain,
% 3.19/0.97      ( sK1 = k1_xboole_0
% 3.19/0.97      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.19/0.97      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.19/0.97      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.19/0.97      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_4353,c_2346]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_24,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | ~ v1_funct_1(X0)
% 3.19/0.97      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.19/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2347,plain,
% 3.19/0.97      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.19/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.97      | v1_funct_1(X2) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4719,plain,
% 3.19/0.97      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.19/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2344,c_2347]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_33,negated_conjecture,
% 3.19/0.97      ( v1_funct_1(sK3) ),
% 3.19/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2703,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/0.97      | ~ v1_funct_1(sK3)
% 3.19/0.97      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_24]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2784,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/0.97      | ~ v1_funct_1(sK3)
% 3.19/0.97      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2703]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5075,plain,
% 3.19/0.97      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_4719,c_33,c_31,c_2784]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_23,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | ~ v1_funct_1(X0)
% 3.19/0.97      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.19/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2348,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/0.97      | v1_funct_1(X0) != iProver_top
% 3.19/0.97      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4053,plain,
% 3.19/0.97      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.19/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2344,c_2348]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_34,plain,
% 3.19/0.97      ( v1_funct_1(sK3) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2672,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/0.97      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.19/0.97      | ~ v1_funct_1(sK3) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_23]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2779,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.19/0.97      | ~ v1_funct_1(sK3) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2672]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2780,plain,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.19/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2779]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_4214,plain,
% 3.19/0.97      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_4053,c_34,c_36,c_2780]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5084,plain,
% 3.19/0.97      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_5075,c_4214]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5456,plain,
% 3.19/0.97      ( sK1 = k1_xboole_0
% 3.19/0.97      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.19/0.97      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.19/0.97      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.19/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_4874,c_5084]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_26,plain,
% 3.19/0.97      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.19/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.19/0.97      | ~ v1_funct_1(X0)
% 3.19/0.97      | ~ v1_relat_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_28,negated_conjecture,
% 3.19/0.97      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.19/0.97      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.97      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.19/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_841,plain,
% 3.19/0.97      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.19/0.97      | ~ v1_funct_1(X0)
% 3.19/0.97      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.19/0.97      | ~ v1_relat_1(X0)
% 3.19/0.97      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.19/0.97      | k1_relat_1(X0) != sK2
% 3.19/0.97      | sK1 != X1 ),
% 3.19/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_842,plain,
% 3.19/0.97      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.97      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.19/0.97      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.19/0.97      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.19/0.97      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.19/0.97      inference(unflattening,[status(thm)],[c_841]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_12,plain,
% 3.19/0.97      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.19/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5,plain,
% 3.19/0.97      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_359,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | r1_tarski(k2_relat_1(X0),X2)
% 3.19/0.97      | ~ v1_relat_1(X0) ),
% 3.19/0.97      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_363,plain,
% 3.19/0.97      ( r1_tarski(k2_relat_1(X0),X2)
% 3.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.19/0.97      inference(global_propositional_subsumption,[status(thm)],[c_359,c_11]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_364,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.19/0.97      inference(renaming,[status(thm)],[c_363]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_854,plain,
% 3.19/0.97      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.97      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.19/0.97      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.19/0.97      inference(forward_subsumption_resolution,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_842,c_11,c_364]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2332,plain,
% 3.19/0.97      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.19/0.97      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_858,plain,
% 3.19/0.97      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.19/0.97      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2838,plain,
% 3.19/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.19/0.97      | ~ v1_funct_1(sK3) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2779]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2839,plain,
% 3.19/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/0.97      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.19/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2838]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2967,plain,
% 3.19/0.97      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.97      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_2332,c_34,c_36,c_858,c_2839]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2968,plain,
% 3.19/0.97      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.19/0.97      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.19/0.97      inference(renaming,[status(thm)],[c_2967]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5080,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.19/0.97      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_5075,c_2968]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5155,plain,
% 3.19/0.97      ( sK1 = k1_xboole_0
% 3.19/0.97      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_4353,c_5080]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5468,plain,
% 3.19/0.97      ( sK1 = k1_xboole_0
% 3.19/0.97      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.19/0.97      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5456,c_5155]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_22,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | ~ v1_funct_1(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2349,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/0.97      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.19/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5133,plain,
% 3.19/0.97      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.19/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5075,c_2349]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5269,plain,
% 3.19/0.97      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_5133,c_34,c_36]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2352,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/0.97      | v1_relat_1(X0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5284,plain,
% 3.19/0.97      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5269,c_2352]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2341,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/0.97      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5281,plain,
% 3.19/0.97      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5269,c_2341]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6063,plain,
% 3.19/0.97      ( sK1 = k1_xboole_0 ),
% 3.19/0.97      inference(forward_subsumption_resolution,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_5468,c_5284,c_5281]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6069,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.19/0.97      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_6063,c_5080]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_29,negated_conjecture,
% 3.19/0.97      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.19/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6080,plain,
% 3.19/0.97      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_6063,c_29]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6081,plain,
% 3.19/0.97      ( sK0 = k1_xboole_0 ),
% 3.19/0.97      inference(equality_resolution_simp,[status(thm)],[c_6080]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6343,plain,
% 3.19/0.97      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_6081,c_2345]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_8,plain,
% 3.19/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3920,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 3.19/0.97      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.19/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_8,c_2354]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.19/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2355,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_13,plain,
% 3.19/0.97      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.19/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6,plain,
% 3.19/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.19/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_339,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | ~ v1_relat_1(X0)
% 3.19/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.19/0.97      inference(resolution,[status(thm)],[c_13,c_6]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_343,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_339,c_13,c_11,c_6]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2342,plain,
% 3.19/0.97      ( k7_relat_1(X0,X1) = X0
% 3.19/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3291,plain,
% 3.19/0.97      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2355,c_2342]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3933,plain,
% 3.19/0.97      ( k1_xboole_0 = X0
% 3.19/0.97      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.19/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.19/0.97      inference(light_normalisation,[status(thm)],[c_3920,c_8,c_3291]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2611,plain,
% 3.19/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/0.97      | v1_relat_1(k1_xboole_0) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2613,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.97      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2611]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2612,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2615,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2612]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3947,plain,
% 3.19/0.97      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_3933,c_2613,c_2615]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3948,plain,
% 3.19/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.19/0.97      inference(renaming,[status(thm)],[c_3947]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6372,plain,
% 3.19/0.97      ( sK2 = k1_xboole_0 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_6343,c_3948]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3292,plain,
% 3.19/0.97      ( k7_relat_1(sK3,sK0) = sK3 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2344,c_2342]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6342,plain,
% 3.19/0.97      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_6081,c_3292]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_0,plain,
% 3.19/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2358,plain,
% 3.19/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_14,plain,
% 3.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.97      | ~ v1_xboole_0(X1)
% 3.19/0.97      | v1_xboole_0(X0) ),
% 3.19/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2351,plain,
% 3.19/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/0.97      | v1_xboole_0(X1) != iProver_top
% 3.19/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5282,plain,
% 3.19/0.97      ( v1_xboole_0(k7_relat_1(sK3,X0)) = iProver_top
% 3.19/0.97      | v1_xboole_0(sK0) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5269,c_2351]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2,plain,
% 3.19/0.97      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.19/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2356,plain,
% 3.19/0.97      ( X0 = X1
% 3.19/0.97      | v1_xboole_0(X1) != iProver_top
% 3.19/0.97      | v1_xboole_0(X0) != iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_5844,plain,
% 3.19/0.97      ( k7_relat_1(sK3,X0) = X1
% 3.19/0.97      | v1_xboole_0(X1) != iProver_top
% 3.19/0.97      | v1_xboole_0(sK0) != iProver_top ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_5282,c_2356]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_103,plain,
% 3.19/0.97      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_108,plain,
% 3.19/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_1857,plain,
% 3.19/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.19/0.97      theory(equality) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2807,plain,
% 3.19/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_1857]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2808,plain,
% 3.19/0.97      ( sK0 != X0
% 3.19/0.97      | v1_xboole_0(X0) != iProver_top
% 3.19/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 3.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2807]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2810,plain,
% 3.19/0.97      ( sK0 != k1_xboole_0
% 3.19/0.97      | v1_xboole_0(sK0) = iProver_top
% 3.19/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2808]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_1856,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2659,plain,
% 3.19/0.97      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2899,plain,
% 3.19/0.97      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_2659]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_1855,plain,( X0 = X0 ),theory(equality) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_2900,plain,
% 3.19/0.97      ( sK0 = sK0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_1855]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3421,plain,
% 3.19/0.97      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_3422,plain,
% 3.19/0.97      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.97      inference(instantiation,[status(thm)],[c_3421]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6831,plain,
% 3.19/0.97      ( v1_xboole_0(X1) != iProver_top | k7_relat_1(sK3,X0) = X1 ),
% 3.19/0.97      inference(global_propositional_subsumption,
% 3.19/0.97                [status(thm)],
% 3.19/0.97                [c_5844,c_29,c_103,c_0,c_108,c_2810,c_2899,c_2900,c_3422,
% 3.19/0.97                 c_6063]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6832,plain,
% 3.19/0.97      ( k7_relat_1(sK3,X0) = X1 | v1_xboole_0(X1) != iProver_top ),
% 3.19/0.97      inference(renaming,[status(thm)],[c_6831]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_6839,plain,
% 3.19/0.97      ( k7_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.19/0.97      inference(superposition,[status(thm)],[c_2358,c_6832]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_7198,plain,
% 3.19/0.97      ( sK3 = k1_xboole_0 ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_6342,c_6839]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_7900,plain,
% 3.19/0.97      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 3.19/0.97      | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.19/0.97      inference(light_normalisation,[status(thm)],[c_6069,c_6372,c_7198]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_7901,plain,
% 3.19/0.97      ( k1_xboole_0 != k1_xboole_0
% 3.19/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.19/0.97      inference(demodulation,[status(thm)],[c_7900,c_8,c_3291]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_7902,plain,
% 3.19/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.19/0.97      inference(equality_resolution_simp,[status(thm)],[c_7901]) ).
% 3.19/0.97  
% 3.19/0.97  cnf(c_7904,plain,
% 3.19/0.97      ( $false ),
% 3.19/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_7902,c_2355]) ).
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.97  
% 3.19/0.97  ------                               Statistics
% 3.19/0.97  
% 3.19/0.97  ------ General
% 3.19/0.97  
% 3.19/0.97  abstr_ref_over_cycles:                  0
% 3.19/0.97  abstr_ref_under_cycles:                 0
% 3.19/0.97  gc_basic_clause_elim:                   0
% 3.19/0.97  forced_gc_time:                         0
% 3.19/0.97  parsing_time:                           0.011
% 3.19/0.97  unif_index_cands_time:                  0.
% 3.19/0.97  unif_index_add_time:                    0.
% 3.19/0.97  orderings_time:                         0.
% 3.19/0.97  out_proof_time:                         0.012
% 3.19/0.97  total_time:                             0.226
% 3.19/0.97  num_of_symbols:                         51
% 3.19/0.97  num_of_terms:                           5967
% 3.19/0.97  
% 3.19/0.97  ------ Preprocessing
% 3.19/0.97  
% 3.19/0.97  num_of_splits:                          0
% 3.19/0.97  num_of_split_atoms:                     0
% 3.19/0.97  num_of_reused_defs:                     0
% 3.19/0.97  num_eq_ax_congr_red:                    15
% 3.19/0.97  num_of_sem_filtered_clauses:            1
% 3.19/0.97  num_of_subtypes:                        0
% 3.19/0.97  monotx_restored_types:                  0
% 3.19/0.97  sat_num_of_epr_types:                   0
% 3.19/0.97  sat_num_of_non_cyclic_types:            0
% 3.19/0.97  sat_guarded_non_collapsed_types:        0
% 3.19/0.97  num_pure_diseq_elim:                    0
% 3.19/0.97  simp_replaced_by:                       0
% 3.19/0.97  res_preprocessed:                       154
% 3.19/0.97  prep_upred:                             0
% 3.19/0.97  prep_unflattend:                        86
% 3.19/0.97  smt_new_axioms:                         0
% 3.19/0.97  pred_elim_cands:                        5
% 3.19/0.97  pred_elim:                              3
% 3.19/0.97  pred_elim_cl:                           1
% 3.19/0.97  pred_elim_cycles:                       9
% 3.19/0.97  merged_defs:                            0
% 3.19/0.97  merged_defs_ncl:                        0
% 3.19/0.97  bin_hyper_res:                          0
% 3.19/0.97  prep_cycles:                            4
% 3.19/0.97  pred_elim_time:                         0.023
% 3.19/0.97  splitting_time:                         0.
% 3.19/0.97  sem_filter_time:                        0.
% 3.19/0.97  monotx_time:                            0.001
% 3.19/0.97  subtype_inf_time:                       0.
% 3.19/0.97  
% 3.19/0.97  ------ Problem properties
% 3.19/0.97  
% 3.19/0.97  clauses:                                32
% 3.19/0.97  conjectures:                            4
% 3.19/0.97  epr:                                    6
% 3.19/0.97  horn:                                   28
% 3.19/0.97  ground:                                 15
% 3.19/0.97  unary:                                  8
% 3.19/0.97  binary:                                 6
% 3.19/0.97  lits:                                   88
% 3.19/0.97  lits_eq:                                32
% 3.19/0.97  fd_pure:                                0
% 3.19/0.97  fd_pseudo:                              0
% 3.19/0.97  fd_cond:                                2
% 3.19/0.97  fd_pseudo_cond:                         1
% 3.19/0.97  ac_symbols:                             0
% 3.19/0.97  
% 3.19/0.97  ------ Propositional Solver
% 3.19/0.97  
% 3.19/0.97  prop_solver_calls:                      29
% 3.19/0.97  prop_fast_solver_calls:                 1376
% 3.19/0.97  smt_solver_calls:                       0
% 3.19/0.97  smt_fast_solver_calls:                  0
% 3.19/0.97  prop_num_of_clauses:                    2741
% 3.19/0.97  prop_preprocess_simplified:             7825
% 3.19/0.97  prop_fo_subsumed:                       34
% 3.19/0.97  prop_solver_time:                       0.
% 3.19/0.97  smt_solver_time:                        0.
% 3.19/0.97  smt_fast_solver_time:                   0.
% 3.19/0.97  prop_fast_solver_time:                  0.
% 3.19/0.97  prop_unsat_core_time:                   0.
% 3.19/0.97  
% 3.19/0.97  ------ QBF
% 3.19/0.97  
% 3.19/0.97  qbf_q_res:                              0
% 3.19/0.97  qbf_num_tautologies:                    0
% 3.19/0.97  qbf_prep_cycles:                        0
% 3.19/0.97  
% 3.19/0.97  ------ BMC1
% 3.19/0.97  
% 3.19/0.97  bmc1_current_bound:                     -1
% 3.19/0.97  bmc1_last_solved_bound:                 -1
% 3.19/0.97  bmc1_unsat_core_size:                   -1
% 3.19/0.97  bmc1_unsat_core_parents_size:           -1
% 3.19/0.97  bmc1_merge_next_fun:                    0
% 3.19/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.97  
% 3.19/0.97  ------ Instantiation
% 3.19/0.97  
% 3.19/0.97  inst_num_of_clauses:                    757
% 3.19/0.97  inst_num_in_passive:                    417
% 3.19/0.97  inst_num_in_active:                     333
% 3.19/0.97  inst_num_in_unprocessed:                8
% 3.19/0.97  inst_num_of_loops:                      420
% 3.19/0.97  inst_num_of_learning_restarts:          0
% 3.19/0.97  inst_num_moves_active_passive:          84
% 3.19/0.97  inst_lit_activity:                      0
% 3.19/0.97  inst_lit_activity_moves:                0
% 3.19/0.97  inst_num_tautologies:                   0
% 3.19/0.97  inst_num_prop_implied:                  0
% 3.19/0.97  inst_num_existing_simplified:           0
% 3.19/0.97  inst_num_eq_res_simplified:             0
% 3.19/0.97  inst_num_child_elim:                    0
% 3.19/0.97  inst_num_of_dismatching_blockings:      263
% 3.19/0.97  inst_num_of_non_proper_insts:           584
% 3.19/0.97  inst_num_of_duplicates:                 0
% 3.19/0.97  inst_inst_num_from_inst_to_res:         0
% 3.19/0.97  inst_dismatching_checking_time:         0.
% 3.19/0.97  
% 3.19/0.97  ------ Resolution
% 3.19/0.97  
% 3.19/0.97  res_num_of_clauses:                     0
% 3.19/0.97  res_num_in_passive:                     0
% 3.19/0.97  res_num_in_active:                      0
% 3.19/0.97  res_num_of_loops:                       158
% 3.19/0.97  res_forward_subset_subsumed:            27
% 3.19/0.97  res_backward_subset_subsumed:           2
% 3.19/0.97  res_forward_subsumed:                   0
% 3.19/0.97  res_backward_subsumed:                  0
% 3.19/0.97  res_forward_subsumption_resolution:     6
% 3.19/0.97  res_backward_subsumption_resolution:    0
% 3.19/0.97  res_clause_to_clause_subsumption:       308
% 3.19/0.97  res_orphan_elimination:                 0
% 3.19/0.97  res_tautology_del:                      61
% 3.19/0.97  res_num_eq_res_simplified:              1
% 3.19/0.97  res_num_sel_changes:                    0
% 3.19/0.97  res_moves_from_active_to_pass:          0
% 3.19/0.97  
% 3.19/0.97  ------ Superposition
% 3.19/0.97  
% 3.19/0.97  sup_time_total:                         0.
% 3.19/0.97  sup_time_generating:                    0.
% 3.19/0.97  sup_time_sim_full:                      0.
% 3.19/0.97  sup_time_sim_immed:                     0.
% 3.19/0.97  
% 3.19/0.97  sup_num_of_clauses:                     79
% 3.19/0.97  sup_num_in_active:                      36
% 3.19/0.97  sup_num_in_passive:                     43
% 3.19/0.97  sup_num_of_loops:                       82
% 3.19/0.97  sup_fw_superposition:                   52
% 3.19/0.97  sup_bw_superposition:                   66
% 3.19/0.97  sup_immediate_simplified:               42
% 3.19/0.97  sup_given_eliminated:                   0
% 3.19/0.97  comparisons_done:                       0
% 3.19/0.97  comparisons_avoided:                    16
% 3.19/0.97  
% 3.19/0.97  ------ Simplifications
% 3.19/0.97  
% 3.19/0.97  
% 3.19/0.97  sim_fw_subset_subsumed:                 14
% 3.19/0.97  sim_bw_subset_subsumed:                 9
% 3.19/0.97  sim_fw_subsumed:                        13
% 3.19/0.97  sim_bw_subsumed:                        0
% 3.19/0.97  sim_fw_subsumption_res:                 8
% 3.19/0.97  sim_bw_subsumption_res:                 0
% 3.19/0.97  sim_tautology_del:                      7
% 3.19/0.97  sim_eq_tautology_del:                   11
% 3.19/0.97  sim_eq_res_simp:                        5
% 3.19/0.97  sim_fw_demodulated:                     10
% 3.19/0.97  sim_bw_demodulated:                     42
% 3.19/0.97  sim_light_normalised:                   32
% 3.19/0.97  sim_joinable_taut:                      0
% 3.19/0.97  sim_joinable_simp:                      0
% 3.19/0.97  sim_ac_normalised:                      0
% 3.19/0.97  sim_smt_subsumption:                    0
% 3.19/0.97  
%------------------------------------------------------------------------------
