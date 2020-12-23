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
% DateTime   : Thu Dec  3 12:03:59 EST 2020

% Result     : Theorem 22.92s
% Output     : CNFRefutation 22.92s
% Verified   : 
% Statistics : Number of formulae       :  345 (1773 expanded)
%              Number of clauses        :  257 ( 829 expanded)
%              Number of leaves         :   30 ( 324 expanded)
%              Depth                    :   21
%              Number of atoms          :  991 (6906 expanded)
%              Number of equality atoms :  577 (2127 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f61,plain,
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

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f61])).

fof(f102,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f100,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_82743,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1236,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_82566,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(X2,X3,X4,X5),X6)
    | X6 != X1
    | k2_partfun1(X2,X3,X4,X5) != X0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_82568,plain,
    ( r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_82566])).

cnf(c_1235,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_82411,plain,
    ( k1_relat_1(X0) != X1
    | sK2 != X1
    | sK2 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_82412,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK2 = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_82411])).

cnf(c_79222,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_81854,plain,
    ( ~ r1_tarski(k2_partfun1(X0,X1,X2,X3),X4)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X5)
    | X5 != X4
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_79222])).

cnf(c_81862,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_81854])).

cnf(c_79208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_zfmisc_1(sK2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_81855,plain,
    ( ~ r1_tarski(k2_partfun1(X0,X1,X2,X3),X4)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3)
    | k2_zfmisc_1(sK2,sK1) != X4 ),
    inference(instantiation,[status(thm)],[c_79208])).

cnf(c_81858,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK2,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_81855])).

cnf(c_79234,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_81837,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_79234])).

cnf(c_81838,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_81837])).

cnf(c_18,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_81815,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1241,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_80846,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_80848,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_80846])).

cnf(c_80809,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_80845,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
    | sK2 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_80809])).

cnf(c_80847,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
    | sK2 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_80845])).

cnf(c_1234,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_80676,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_1240,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_78540,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_79227,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_78540])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_78504,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9293,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_65310,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9293])).

cnf(c_1237,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_21814,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_58546,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,X0)
    | sK2 != sK2
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_21814])).

cnf(c_58547,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
    | sK2 != sK2
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_58546])).

cnf(c_9088,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_11706,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1)
    | X1 != X0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9088])).

cnf(c_57886,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | X0 != sK1
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11706])).

cnf(c_57888,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_57886])).

cnf(c_13725,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_37074,plain,
    ( k2_zfmisc_1(sK2,sK1) != X0
    | k2_zfmisc_1(sK2,sK1) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_13725])).

cnf(c_56116,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,k1_xboole_0)
    | k2_zfmisc_1(sK2,sK1) = sK1
    | sK1 != k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_37074])).

cnf(c_1245,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_50546,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,X1,X2,X3)
    | sK2 != X3
    | sK3 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_50551,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_50546])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2514,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_9251,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_50100,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_9251])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2044,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2062,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3328,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2062])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2066,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5130,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_2066])).

cnf(c_2063,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_12])).

cnf(c_2041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_4300,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2063,c_2041])).

cnf(c_12565,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_4300])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_386,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_317])).

cnf(c_2042,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_5550,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_2042])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2058,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13307,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5550,c_2058])).

cnf(c_14733,plain,
    ( r1_tarski(k2_relat_1(X0),sK1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12565,c_13307])).

cnf(c_14734,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_14733])).

cnf(c_4831,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_2042])).

cnf(c_5433,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4831,c_2058])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2055,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2064,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3492,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2064])).

cnf(c_5436,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5433,c_3492])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5975,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_2062])).

cnf(c_46670,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5436,c_5975])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_46921,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46670,c_4])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2409,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2410,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_2412,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_9294,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9293])).

cnf(c_9296,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9294])).

cnf(c_47072,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46921,c_43,c_2412,c_5433,c_9296])).

cnf(c_47084,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14734,c_47072])).

cnf(c_12075,plain,
    ( k2_zfmisc_1(sK2,sK1) != X0
    | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_37075,plain,
    ( k2_zfmisc_1(sK2,sK1) != sK1
    | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_12075])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2045,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_41])).

cnf(c_765,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_767,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_765,c_40])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2048,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3682,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2044,c_2048])).

cnf(c_3821,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_767,c_3682])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2052,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5212,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3821,c_2052])).

cnf(c_8460,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5212,c_5433])).

cnf(c_8461,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8460])).

cnf(c_8471,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2045,c_8461])).

cnf(c_8555,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8471,c_2046])).

cnf(c_2047,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6254,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2047])).

cnf(c_6456,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6254,c_43])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_775,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_776,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_788,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_776,c_512])).

cnf(c_2032,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_6462,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6456,c_2032])).

cnf(c_8565,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8471,c_6462])).

cnf(c_9762,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8555,c_8565])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2057,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6135,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_2057])).

cnf(c_6359,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_5433,c_6135])).

cnf(c_2050,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k7_relat_1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6515,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6359,c_2050])).

cnf(c_25,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2049,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3606,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2049])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2056,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4497,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_2056])).

cnf(c_1243,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2431,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_3739,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | k7_relat_1(sK3,X0) != sK3 ),
    inference(instantiation,[status(thm)],[c_2431])).

cnf(c_11036,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | k7_relat_1(sK3,sK0) != sK3 ),
    inference(instantiation,[status(thm)],[c_3739])).

cnf(c_11037,plain,
    ( k7_relat_1(sK3,sK0) != sK3
    | v1_funct_1(k7_relat_1(sK3,sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11036])).

cnf(c_22002,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6515,c_43,c_4497,c_5433,c_11037])).

cnf(c_5439,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(superposition,[status(thm)],[c_5433,c_4497])).

cnf(c_22006,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22002,c_5439])).

cnf(c_22009,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22006,c_5433])).

cnf(c_35660,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9762,c_22009])).

cnf(c_35661,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_35660])).

cnf(c_35669,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14734,c_35661])).

cnf(c_35692,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_35669])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5972,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3821,c_2046])).

cnf(c_9628,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5972,c_43,c_5433])).

cnf(c_9638,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9628,c_2062])).

cnf(c_30581,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_9638])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_137,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_138,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_142,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_144,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_3369,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_3370,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_3423,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2684,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3844,plain,
    ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_3849,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_3851,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3849])).

cnf(c_6573,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X3),k1_xboole_0)
    | k2_zfmisc_1(X2,X3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_6574,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X3
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6573])).

cnf(c_6576,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6574])).

cnf(c_2741,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_4889,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k2_zfmisc_1(X2,X3))
    | k2_zfmisc_1(X2,X3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_5922,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_10183,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,X1))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5922])).

cnf(c_10184,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10183])).

cnf(c_10186,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10184])).

cnf(c_11618,plain,
    ( X0 != sK1
    | X1 != sK0
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_11619,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_11618])).

cnf(c_31895,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30581,c_38,c_137,c_138,c_144,c_3328,c_3370,c_3423,c_3851,c_6576,c_10186,c_11619])).

cnf(c_31897,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_31895])).

cnf(c_24637,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_24642,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24637])).

cnf(c_24644,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24642])).

cnf(c_2522,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k7_relat_1(sK3,X1))
    | X0 != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_10970,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(k7_relat_1(sK3,X0))
    | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_22239,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_10970])).

cnf(c_22010,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22009])).

cnf(c_3475,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_7116,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3475])).

cnf(c_13961,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_5473,plain,
    ( X0 != X1
    | k2_zfmisc_1(sK2,k1_xboole_0) != X1
    | k2_zfmisc_1(sK2,k1_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_13732,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
    | k2_zfmisc_1(sK2,k1_xboole_0) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_5473])).

cnf(c_13733,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) = sK1
    | k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13732])).

cnf(c_2577,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_3352,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2577])).

cnf(c_13731,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != sK1
    | sK1 = k2_zfmisc_1(sK2,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3352])).

cnf(c_11707,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_9172,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9175,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,X0)
    | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9172])).

cnf(c_9177,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9175])).

cnf(c_2054,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3321,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_2064])).

cnf(c_112,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_114,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_2414,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_2415,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_2417,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_2734,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2737,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2734])).

cnf(c_2739,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2737])).

cnf(c_3428,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_114,c_2417,c_2739])).

cnf(c_3491,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_2055])).

cnf(c_3560,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3491,c_114,c_2417,c_2739])).

cnf(c_3567,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3560,c_2064])).

cnf(c_5971,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_2046])).

cnf(c_6035,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5971,c_4])).

cnf(c_134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_136,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_7223,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6035,c_136,c_144])).

cnf(c_6255,plain,
    ( k2_partfun1(X0,k1_xboole_0,X1,X2) = k7_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2047])).

cnf(c_7230,plain,
    ( k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1) = k7_relat_1(k1_xboole_0,X1)
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_6255])).

cnf(c_7247,plain,
    ( k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7230,c_3428])).

cnf(c_7261,plain,
    ( k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7247])).

cnf(c_2059,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6519,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6359,c_2059])).

cnf(c_6551,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6519])).

cnf(c_2713,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_5960,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2713])).

cnf(c_5962,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_5960])).

cnf(c_5471,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5434,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5433])).

cnf(c_4301,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2041])).

cnf(c_4323,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4301])).

cnf(c_2758,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2582,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2480,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_2581,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2480])).

cnf(c_2579,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2479,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_2578,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2479])).

cnf(c_2576,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2547,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2528,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_2530,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_143,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_82743,c_82568,c_82412,c_81862,c_81858,c_81838,c_81815,c_80848,c_80847,c_80676,c_79227,c_78504,c_65310,c_58547,c_57888,c_56116,c_50551,c_50100,c_47084,c_37075,c_35692,c_31897,c_24644,c_22239,c_22010,c_13961,c_13733,c_13731,c_11707,c_9177,c_7261,c_6551,c_5962,c_5471,c_5434,c_5433,c_4323,c_3567,c_3423,c_3370,c_2758,c_2582,c_2581,c_2579,c_2578,c_2576,c_2547,c_2530,c_2412,c_788,c_143,c_138,c_137,c_38,c_39,c_40,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 22.92/4.64  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.92/4.64  
% 22.92/4.64  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.92/4.64  
% 22.92/4.64  ------  iProver source info
% 22.92/4.64  
% 22.92/4.64  git: date: 2020-06-30 10:37:57 +0100
% 22.92/4.64  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.92/4.64  git: non_committed_changes: false
% 22.92/4.64  git: last_make_outside_of_git: false
% 22.92/4.64  
% 22.92/4.64  ------ 
% 22.92/4.64  
% 22.92/4.64  ------ Input Options
% 22.92/4.64  
% 22.92/4.64  --out_options                           all
% 22.92/4.64  --tptp_safe_out                         true
% 22.92/4.64  --problem_path                          ""
% 22.92/4.64  --include_path                          ""
% 22.92/4.64  --clausifier                            res/vclausify_rel
% 22.92/4.64  --clausifier_options                    --mode clausify
% 22.92/4.64  --stdin                                 false
% 22.92/4.64  --stats_out                             all
% 22.92/4.64  
% 22.92/4.64  ------ General Options
% 22.92/4.64  
% 22.92/4.64  --fof                                   false
% 22.92/4.64  --time_out_real                         305.
% 22.92/4.64  --time_out_virtual                      -1.
% 22.92/4.64  --symbol_type_check                     false
% 22.92/4.64  --clausify_out                          false
% 22.92/4.64  --sig_cnt_out                           false
% 22.92/4.64  --trig_cnt_out                          false
% 22.92/4.64  --trig_cnt_out_tolerance                1.
% 22.92/4.64  --trig_cnt_out_sk_spl                   false
% 22.92/4.64  --abstr_cl_out                          false
% 22.92/4.64  
% 22.92/4.64  ------ Global Options
% 22.92/4.64  
% 22.92/4.64  --schedule                              default
% 22.92/4.64  --add_important_lit                     false
% 22.92/4.64  --prop_solver_per_cl                    1000
% 22.92/4.64  --min_unsat_core                        false
% 22.92/4.64  --soft_assumptions                      false
% 22.92/4.64  --soft_lemma_size                       3
% 22.92/4.64  --prop_impl_unit_size                   0
% 22.92/4.64  --prop_impl_unit                        []
% 22.92/4.64  --share_sel_clauses                     true
% 22.92/4.64  --reset_solvers                         false
% 22.92/4.64  --bc_imp_inh                            [conj_cone]
% 22.92/4.64  --conj_cone_tolerance                   3.
% 22.92/4.64  --extra_neg_conj                        none
% 22.92/4.64  --large_theory_mode                     true
% 22.92/4.64  --prolific_symb_bound                   200
% 22.92/4.64  --lt_threshold                          2000
% 22.92/4.64  --clause_weak_htbl                      true
% 22.92/4.64  --gc_record_bc_elim                     false
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing Options
% 22.92/4.64  
% 22.92/4.64  --preprocessing_flag                    true
% 22.92/4.64  --time_out_prep_mult                    0.1
% 22.92/4.64  --splitting_mode                        input
% 22.92/4.64  --splitting_grd                         true
% 22.92/4.64  --splitting_cvd                         false
% 22.92/4.64  --splitting_cvd_svl                     false
% 22.92/4.64  --splitting_nvd                         32
% 22.92/4.64  --sub_typing                            true
% 22.92/4.64  --prep_gs_sim                           true
% 22.92/4.64  --prep_unflatten                        true
% 22.92/4.64  --prep_res_sim                          true
% 22.92/4.64  --prep_upred                            true
% 22.92/4.64  --prep_sem_filter                       exhaustive
% 22.92/4.64  --prep_sem_filter_out                   false
% 22.92/4.64  --pred_elim                             true
% 22.92/4.64  --res_sim_input                         true
% 22.92/4.64  --eq_ax_congr_red                       true
% 22.92/4.64  --pure_diseq_elim                       true
% 22.92/4.64  --brand_transform                       false
% 22.92/4.64  --non_eq_to_eq                          false
% 22.92/4.64  --prep_def_merge                        true
% 22.92/4.64  --prep_def_merge_prop_impl              false
% 22.92/4.64  --prep_def_merge_mbd                    true
% 22.92/4.64  --prep_def_merge_tr_red                 false
% 22.92/4.64  --prep_def_merge_tr_cl                  false
% 22.92/4.64  --smt_preprocessing                     true
% 22.92/4.64  --smt_ac_axioms                         fast
% 22.92/4.64  --preprocessed_out                      false
% 22.92/4.64  --preprocessed_stats                    false
% 22.92/4.64  
% 22.92/4.64  ------ Abstraction refinement Options
% 22.92/4.64  
% 22.92/4.64  --abstr_ref                             []
% 22.92/4.64  --abstr_ref_prep                        false
% 22.92/4.64  --abstr_ref_until_sat                   false
% 22.92/4.64  --abstr_ref_sig_restrict                funpre
% 22.92/4.64  --abstr_ref_af_restrict_to_split_sk     false
% 22.92/4.64  --abstr_ref_under                       []
% 22.92/4.64  
% 22.92/4.64  ------ SAT Options
% 22.92/4.64  
% 22.92/4.64  --sat_mode                              false
% 22.92/4.64  --sat_fm_restart_options                ""
% 22.92/4.64  --sat_gr_def                            false
% 22.92/4.64  --sat_epr_types                         true
% 22.92/4.64  --sat_non_cyclic_types                  false
% 22.92/4.64  --sat_finite_models                     false
% 22.92/4.64  --sat_fm_lemmas                         false
% 22.92/4.64  --sat_fm_prep                           false
% 22.92/4.64  --sat_fm_uc_incr                        true
% 22.92/4.64  --sat_out_model                         small
% 22.92/4.64  --sat_out_clauses                       false
% 22.92/4.64  
% 22.92/4.64  ------ QBF Options
% 22.92/4.64  
% 22.92/4.64  --qbf_mode                              false
% 22.92/4.64  --qbf_elim_univ                         false
% 22.92/4.64  --qbf_dom_inst                          none
% 22.92/4.64  --qbf_dom_pre_inst                      false
% 22.92/4.64  --qbf_sk_in                             false
% 22.92/4.64  --qbf_pred_elim                         true
% 22.92/4.64  --qbf_split                             512
% 22.92/4.64  
% 22.92/4.64  ------ BMC1 Options
% 22.92/4.64  
% 22.92/4.64  --bmc1_incremental                      false
% 22.92/4.64  --bmc1_axioms                           reachable_all
% 22.92/4.64  --bmc1_min_bound                        0
% 22.92/4.64  --bmc1_max_bound                        -1
% 22.92/4.64  --bmc1_max_bound_default                -1
% 22.92/4.64  --bmc1_symbol_reachability              true
% 22.92/4.64  --bmc1_property_lemmas                  false
% 22.92/4.64  --bmc1_k_induction                      false
% 22.92/4.64  --bmc1_non_equiv_states                 false
% 22.92/4.64  --bmc1_deadlock                         false
% 22.92/4.64  --bmc1_ucm                              false
% 22.92/4.64  --bmc1_add_unsat_core                   none
% 22.92/4.64  --bmc1_unsat_core_children              false
% 22.92/4.64  --bmc1_unsat_core_extrapolate_axioms    false
% 22.92/4.64  --bmc1_out_stat                         full
% 22.92/4.64  --bmc1_ground_init                      false
% 22.92/4.64  --bmc1_pre_inst_next_state              false
% 22.92/4.64  --bmc1_pre_inst_state                   false
% 22.92/4.64  --bmc1_pre_inst_reach_state             false
% 22.92/4.64  --bmc1_out_unsat_core                   false
% 22.92/4.64  --bmc1_aig_witness_out                  false
% 22.92/4.64  --bmc1_verbose                          false
% 22.92/4.64  --bmc1_dump_clauses_tptp                false
% 22.92/4.64  --bmc1_dump_unsat_core_tptp             false
% 22.92/4.64  --bmc1_dump_file                        -
% 22.92/4.64  --bmc1_ucm_expand_uc_limit              128
% 22.92/4.64  --bmc1_ucm_n_expand_iterations          6
% 22.92/4.64  --bmc1_ucm_extend_mode                  1
% 22.92/4.64  --bmc1_ucm_init_mode                    2
% 22.92/4.64  --bmc1_ucm_cone_mode                    none
% 22.92/4.64  --bmc1_ucm_reduced_relation_type        0
% 22.92/4.64  --bmc1_ucm_relax_model                  4
% 22.92/4.64  --bmc1_ucm_full_tr_after_sat            true
% 22.92/4.64  --bmc1_ucm_expand_neg_assumptions       false
% 22.92/4.64  --bmc1_ucm_layered_model                none
% 22.92/4.64  --bmc1_ucm_max_lemma_size               10
% 22.92/4.64  
% 22.92/4.64  ------ AIG Options
% 22.92/4.64  
% 22.92/4.64  --aig_mode                              false
% 22.92/4.64  
% 22.92/4.64  ------ Instantiation Options
% 22.92/4.64  
% 22.92/4.64  --instantiation_flag                    true
% 22.92/4.64  --inst_sos_flag                         false
% 22.92/4.64  --inst_sos_phase                        true
% 22.92/4.64  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.92/4.64  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.92/4.64  --inst_lit_sel_side                     num_symb
% 22.92/4.64  --inst_solver_per_active                1400
% 22.92/4.64  --inst_solver_calls_frac                1.
% 22.92/4.64  --inst_passive_queue_type               priority_queues
% 22.92/4.64  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.92/4.64  --inst_passive_queues_freq              [25;2]
% 22.92/4.64  --inst_dismatching                      true
% 22.92/4.64  --inst_eager_unprocessed_to_passive     true
% 22.92/4.64  --inst_prop_sim_given                   true
% 22.92/4.64  --inst_prop_sim_new                     false
% 22.92/4.64  --inst_subs_new                         false
% 22.92/4.64  --inst_eq_res_simp                      false
% 22.92/4.64  --inst_subs_given                       false
% 22.92/4.64  --inst_orphan_elimination               true
% 22.92/4.64  --inst_learning_loop_flag               true
% 22.92/4.64  --inst_learning_start                   3000
% 22.92/4.64  --inst_learning_factor                  2
% 22.92/4.64  --inst_start_prop_sim_after_learn       3
% 22.92/4.64  --inst_sel_renew                        solver
% 22.92/4.64  --inst_lit_activity_flag                true
% 22.92/4.64  --inst_restr_to_given                   false
% 22.92/4.64  --inst_activity_threshold               500
% 22.92/4.64  --inst_out_proof                        true
% 22.92/4.64  
% 22.92/4.64  ------ Resolution Options
% 22.92/4.64  
% 22.92/4.64  --resolution_flag                       true
% 22.92/4.64  --res_lit_sel                           adaptive
% 22.92/4.64  --res_lit_sel_side                      none
% 22.92/4.64  --res_ordering                          kbo
% 22.92/4.64  --res_to_prop_solver                    active
% 22.92/4.64  --res_prop_simpl_new                    false
% 22.92/4.64  --res_prop_simpl_given                  true
% 22.92/4.64  --res_passive_queue_type                priority_queues
% 22.92/4.64  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.92/4.64  --res_passive_queues_freq               [15;5]
% 22.92/4.64  --res_forward_subs                      full
% 22.92/4.64  --res_backward_subs                     full
% 22.92/4.64  --res_forward_subs_resolution           true
% 22.92/4.64  --res_backward_subs_resolution          true
% 22.92/4.64  --res_orphan_elimination                true
% 22.92/4.64  --res_time_limit                        2.
% 22.92/4.64  --res_out_proof                         true
% 22.92/4.64  
% 22.92/4.64  ------ Superposition Options
% 22.92/4.64  
% 22.92/4.64  --superposition_flag                    true
% 22.92/4.64  --sup_passive_queue_type                priority_queues
% 22.92/4.64  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.92/4.64  --sup_passive_queues_freq               [8;1;4]
% 22.92/4.64  --demod_completeness_check              fast
% 22.92/4.64  --demod_use_ground                      true
% 22.92/4.64  --sup_to_prop_solver                    passive
% 22.92/4.64  --sup_prop_simpl_new                    true
% 22.92/4.64  --sup_prop_simpl_given                  true
% 22.92/4.64  --sup_fun_splitting                     false
% 22.92/4.64  --sup_smt_interval                      50000
% 22.92/4.64  
% 22.92/4.64  ------ Superposition Simplification Setup
% 22.92/4.64  
% 22.92/4.64  --sup_indices_passive                   []
% 22.92/4.64  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_full_triv                         [TrivRules;PropSubs]
% 22.92/4.64  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_full_bw                           [BwDemod]
% 22.92/4.64  --sup_immed_triv                        [TrivRules]
% 22.92/4.64  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.92/4.64  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_immed_bw_main                     []
% 22.92/4.64  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.92/4.64  --sup_input_triv                        [Unflattening;TrivRules]
% 22.92/4.64  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.92/4.64  
% 22.92/4.64  ------ Combination Options
% 22.92/4.64  
% 22.92/4.64  --comb_res_mult                         3
% 22.92/4.64  --comb_sup_mult                         2
% 22.92/4.64  --comb_inst_mult                        10
% 22.92/4.64  
% 22.92/4.64  ------ Debug Options
% 22.92/4.64  
% 22.92/4.64  --dbg_backtrace                         false
% 22.92/4.64  --dbg_dump_prop_clauses                 false
% 22.92/4.64  --dbg_dump_prop_clauses_file            -
% 22.92/4.64  --dbg_out_stat                          false
% 22.92/4.64  ------ Parsing...
% 22.92/4.64  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/4.64  ------ Proving...
% 22.92/4.64  ------ Problem Properties 
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  clauses                                 41
% 22.92/4.64  conjectures                             4
% 22.92/4.64  EPR                                     7
% 22.92/4.64  Horn                                    36
% 22.92/4.64  unary                                   7
% 22.92/4.64  binary                                  12
% 22.92/4.64  lits                                    113
% 22.92/4.64  lits eq                                 37
% 22.92/4.64  fd_pure                                 0
% 22.92/4.64  fd_pseudo                               0
% 22.92/4.64  fd_cond                                 4
% 22.92/4.64  fd_pseudo_cond                          0
% 22.92/4.64  AC symbols                              0
% 22.92/4.64  
% 22.92/4.64  ------ Schedule dynamic 5 is on 
% 22.92/4.64  
% 22.92/4.64  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  ------ 
% 22.92/4.64  Current options:
% 22.92/4.64  ------ 
% 22.92/4.64  
% 22.92/4.64  ------ Input Options
% 22.92/4.64  
% 22.92/4.64  --out_options                           all
% 22.92/4.64  --tptp_safe_out                         true
% 22.92/4.64  --problem_path                          ""
% 22.92/4.64  --include_path                          ""
% 22.92/4.64  --clausifier                            res/vclausify_rel
% 22.92/4.64  --clausifier_options                    --mode clausify
% 22.92/4.64  --stdin                                 false
% 22.92/4.64  --stats_out                             all
% 22.92/4.64  
% 22.92/4.64  ------ General Options
% 22.92/4.64  
% 22.92/4.64  --fof                                   false
% 22.92/4.64  --time_out_real                         305.
% 22.92/4.64  --time_out_virtual                      -1.
% 22.92/4.64  --symbol_type_check                     false
% 22.92/4.64  --clausify_out                          false
% 22.92/4.64  --sig_cnt_out                           false
% 22.92/4.64  --trig_cnt_out                          false
% 22.92/4.64  --trig_cnt_out_tolerance                1.
% 22.92/4.64  --trig_cnt_out_sk_spl                   false
% 22.92/4.64  --abstr_cl_out                          false
% 22.92/4.64  
% 22.92/4.64  ------ Global Options
% 22.92/4.64  
% 22.92/4.64  --schedule                              default
% 22.92/4.64  --add_important_lit                     false
% 22.92/4.64  --prop_solver_per_cl                    1000
% 22.92/4.64  --min_unsat_core                        false
% 22.92/4.64  --soft_assumptions                      false
% 22.92/4.64  --soft_lemma_size                       3
% 22.92/4.64  --prop_impl_unit_size                   0
% 22.92/4.64  --prop_impl_unit                        []
% 22.92/4.64  --share_sel_clauses                     true
% 22.92/4.64  --reset_solvers                         false
% 22.92/4.64  --bc_imp_inh                            [conj_cone]
% 22.92/4.64  --conj_cone_tolerance                   3.
% 22.92/4.64  --extra_neg_conj                        none
% 22.92/4.64  --large_theory_mode                     true
% 22.92/4.64  --prolific_symb_bound                   200
% 22.92/4.64  --lt_threshold                          2000
% 22.92/4.64  --clause_weak_htbl                      true
% 22.92/4.64  --gc_record_bc_elim                     false
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing Options
% 22.92/4.64  
% 22.92/4.64  --preprocessing_flag                    true
% 22.92/4.64  --time_out_prep_mult                    0.1
% 22.92/4.64  --splitting_mode                        input
% 22.92/4.64  --splitting_grd                         true
% 22.92/4.64  --splitting_cvd                         false
% 22.92/4.64  --splitting_cvd_svl                     false
% 22.92/4.64  --splitting_nvd                         32
% 22.92/4.64  --sub_typing                            true
% 22.92/4.64  --prep_gs_sim                           true
% 22.92/4.64  --prep_unflatten                        true
% 22.92/4.64  --prep_res_sim                          true
% 22.92/4.64  --prep_upred                            true
% 22.92/4.64  --prep_sem_filter                       exhaustive
% 22.92/4.64  --prep_sem_filter_out                   false
% 22.92/4.64  --pred_elim                             true
% 22.92/4.64  --res_sim_input                         true
% 22.92/4.64  --eq_ax_congr_red                       true
% 22.92/4.64  --pure_diseq_elim                       true
% 22.92/4.64  --brand_transform                       false
% 22.92/4.64  --non_eq_to_eq                          false
% 22.92/4.64  --prep_def_merge                        true
% 22.92/4.64  --prep_def_merge_prop_impl              false
% 22.92/4.64  --prep_def_merge_mbd                    true
% 22.92/4.64  --prep_def_merge_tr_red                 false
% 22.92/4.64  --prep_def_merge_tr_cl                  false
% 22.92/4.64  --smt_preprocessing                     true
% 22.92/4.64  --smt_ac_axioms                         fast
% 22.92/4.64  --preprocessed_out                      false
% 22.92/4.64  --preprocessed_stats                    false
% 22.92/4.64  
% 22.92/4.64  ------ Abstraction refinement Options
% 22.92/4.64  
% 22.92/4.64  --abstr_ref                             []
% 22.92/4.64  --abstr_ref_prep                        false
% 22.92/4.64  --abstr_ref_until_sat                   false
% 22.92/4.64  --abstr_ref_sig_restrict                funpre
% 22.92/4.64  --abstr_ref_af_restrict_to_split_sk     false
% 22.92/4.64  --abstr_ref_under                       []
% 22.92/4.64  
% 22.92/4.64  ------ SAT Options
% 22.92/4.64  
% 22.92/4.64  --sat_mode                              false
% 22.92/4.64  --sat_fm_restart_options                ""
% 22.92/4.64  --sat_gr_def                            false
% 22.92/4.64  --sat_epr_types                         true
% 22.92/4.64  --sat_non_cyclic_types                  false
% 22.92/4.64  --sat_finite_models                     false
% 22.92/4.64  --sat_fm_lemmas                         false
% 22.92/4.64  --sat_fm_prep                           false
% 22.92/4.64  --sat_fm_uc_incr                        true
% 22.92/4.64  --sat_out_model                         small
% 22.92/4.64  --sat_out_clauses                       false
% 22.92/4.64  
% 22.92/4.64  ------ QBF Options
% 22.92/4.64  
% 22.92/4.64  --qbf_mode                              false
% 22.92/4.64  --qbf_elim_univ                         false
% 22.92/4.64  --qbf_dom_inst                          none
% 22.92/4.64  --qbf_dom_pre_inst                      false
% 22.92/4.64  --qbf_sk_in                             false
% 22.92/4.64  --qbf_pred_elim                         true
% 22.92/4.64  --qbf_split                             512
% 22.92/4.64  
% 22.92/4.64  ------ BMC1 Options
% 22.92/4.64  
% 22.92/4.64  --bmc1_incremental                      false
% 22.92/4.64  --bmc1_axioms                           reachable_all
% 22.92/4.64  --bmc1_min_bound                        0
% 22.92/4.64  --bmc1_max_bound                        -1
% 22.92/4.64  --bmc1_max_bound_default                -1
% 22.92/4.64  --bmc1_symbol_reachability              true
% 22.92/4.64  --bmc1_property_lemmas                  false
% 22.92/4.64  --bmc1_k_induction                      false
% 22.92/4.64  --bmc1_non_equiv_states                 false
% 22.92/4.64  --bmc1_deadlock                         false
% 22.92/4.64  --bmc1_ucm                              false
% 22.92/4.64  --bmc1_add_unsat_core                   none
% 22.92/4.64  --bmc1_unsat_core_children              false
% 22.92/4.64  --bmc1_unsat_core_extrapolate_axioms    false
% 22.92/4.64  --bmc1_out_stat                         full
% 22.92/4.64  --bmc1_ground_init                      false
% 22.92/4.64  --bmc1_pre_inst_next_state              false
% 22.92/4.64  --bmc1_pre_inst_state                   false
% 22.92/4.64  --bmc1_pre_inst_reach_state             false
% 22.92/4.64  --bmc1_out_unsat_core                   false
% 22.92/4.64  --bmc1_aig_witness_out                  false
% 22.92/4.64  --bmc1_verbose                          false
% 22.92/4.64  --bmc1_dump_clauses_tptp                false
% 22.92/4.64  --bmc1_dump_unsat_core_tptp             false
% 22.92/4.64  --bmc1_dump_file                        -
% 22.92/4.64  --bmc1_ucm_expand_uc_limit              128
% 22.92/4.64  --bmc1_ucm_n_expand_iterations          6
% 22.92/4.64  --bmc1_ucm_extend_mode                  1
% 22.92/4.64  --bmc1_ucm_init_mode                    2
% 22.92/4.64  --bmc1_ucm_cone_mode                    none
% 22.92/4.64  --bmc1_ucm_reduced_relation_type        0
% 22.92/4.64  --bmc1_ucm_relax_model                  4
% 22.92/4.64  --bmc1_ucm_full_tr_after_sat            true
% 22.92/4.64  --bmc1_ucm_expand_neg_assumptions       false
% 22.92/4.64  --bmc1_ucm_layered_model                none
% 22.92/4.64  --bmc1_ucm_max_lemma_size               10
% 22.92/4.64  
% 22.92/4.64  ------ AIG Options
% 22.92/4.64  
% 22.92/4.64  --aig_mode                              false
% 22.92/4.64  
% 22.92/4.64  ------ Instantiation Options
% 22.92/4.64  
% 22.92/4.64  --instantiation_flag                    true
% 22.92/4.64  --inst_sos_flag                         false
% 22.92/4.64  --inst_sos_phase                        true
% 22.92/4.64  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.92/4.64  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.92/4.64  --inst_lit_sel_side                     none
% 22.92/4.64  --inst_solver_per_active                1400
% 22.92/4.64  --inst_solver_calls_frac                1.
% 22.92/4.64  --inst_passive_queue_type               priority_queues
% 22.92/4.64  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.92/4.64  --inst_passive_queues_freq              [25;2]
% 22.92/4.64  --inst_dismatching                      true
% 22.92/4.64  --inst_eager_unprocessed_to_passive     true
% 22.92/4.64  --inst_prop_sim_given                   true
% 22.92/4.64  --inst_prop_sim_new                     false
% 22.92/4.64  --inst_subs_new                         false
% 22.92/4.64  --inst_eq_res_simp                      false
% 22.92/4.64  --inst_subs_given                       false
% 22.92/4.64  --inst_orphan_elimination               true
% 22.92/4.64  --inst_learning_loop_flag               true
% 22.92/4.64  --inst_learning_start                   3000
% 22.92/4.64  --inst_learning_factor                  2
% 22.92/4.64  --inst_start_prop_sim_after_learn       3
% 22.92/4.64  --inst_sel_renew                        solver
% 22.92/4.64  --inst_lit_activity_flag                true
% 22.92/4.64  --inst_restr_to_given                   false
% 22.92/4.64  --inst_activity_threshold               500
% 22.92/4.64  --inst_out_proof                        true
% 22.92/4.64  
% 22.92/4.64  ------ Resolution Options
% 22.92/4.64  
% 22.92/4.64  --resolution_flag                       false
% 22.92/4.64  --res_lit_sel                           adaptive
% 22.92/4.64  --res_lit_sel_side                      none
% 22.92/4.64  --res_ordering                          kbo
% 22.92/4.64  --res_to_prop_solver                    active
% 22.92/4.64  --res_prop_simpl_new                    false
% 22.92/4.64  --res_prop_simpl_given                  true
% 22.92/4.64  --res_passive_queue_type                priority_queues
% 22.92/4.64  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.92/4.64  --res_passive_queues_freq               [15;5]
% 22.92/4.64  --res_forward_subs                      full
% 22.92/4.64  --res_backward_subs                     full
% 22.92/4.64  --res_forward_subs_resolution           true
% 22.92/4.64  --res_backward_subs_resolution          true
% 22.92/4.64  --res_orphan_elimination                true
% 22.92/4.64  --res_time_limit                        2.
% 22.92/4.64  --res_out_proof                         true
% 22.92/4.64  
% 22.92/4.64  ------ Superposition Options
% 22.92/4.64  
% 22.92/4.64  --superposition_flag                    true
% 22.92/4.64  --sup_passive_queue_type                priority_queues
% 22.92/4.64  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.92/4.64  --sup_passive_queues_freq               [8;1;4]
% 22.92/4.64  --demod_completeness_check              fast
% 22.92/4.64  --demod_use_ground                      true
% 22.92/4.64  --sup_to_prop_solver                    passive
% 22.92/4.64  --sup_prop_simpl_new                    true
% 22.92/4.64  --sup_prop_simpl_given                  true
% 22.92/4.64  --sup_fun_splitting                     false
% 22.92/4.64  --sup_smt_interval                      50000
% 22.92/4.64  
% 22.92/4.64  ------ Superposition Simplification Setup
% 22.92/4.64  
% 22.92/4.64  --sup_indices_passive                   []
% 22.92/4.64  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.92/4.64  --sup_full_triv                         [TrivRules;PropSubs]
% 22.92/4.64  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_full_bw                           [BwDemod]
% 22.92/4.64  --sup_immed_triv                        [TrivRules]
% 22.92/4.64  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.92/4.64  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_immed_bw_main                     []
% 22.92/4.64  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.92/4.64  --sup_input_triv                        [Unflattening;TrivRules]
% 22.92/4.64  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.92/4.64  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.92/4.64  
% 22.92/4.64  ------ Combination Options
% 22.92/4.64  
% 22.92/4.64  --comb_res_mult                         3
% 22.92/4.64  --comb_sup_mult                         2
% 22.92/4.64  --comb_inst_mult                        10
% 22.92/4.64  
% 22.92/4.64  ------ Debug Options
% 22.92/4.64  
% 22.92/4.64  --dbg_backtrace                         false
% 22.92/4.64  --dbg_dump_prop_clauses                 false
% 22.92/4.64  --dbg_dump_prop_clauses_file            -
% 22.92/4.64  --dbg_out_stat                          false
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  ------ Proving...
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  % SZS status Theorem for theBenchmark.p
% 22.92/4.64  
% 22.92/4.64  % SZS output start CNFRefutation for theBenchmark.p
% 22.92/4.64  
% 22.92/4.64  fof(f3,axiom,(
% 22.92/4.64    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f28,plain,(
% 22.92/4.64    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 22.92/4.64    inference(ennf_transformation,[],[f3])).
% 22.92/4.64  
% 22.92/4.64  fof(f65,plain,(
% 22.92/4.64    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f28])).
% 22.92/4.64  
% 22.92/4.64  fof(f14,axiom,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f38,plain,(
% 22.92/4.64    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(ennf_transformation,[],[f14])).
% 22.92/4.64  
% 22.92/4.64  fof(f81,plain,(
% 22.92/4.64    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f38])).
% 22.92/4.64  
% 22.92/4.64  fof(f5,axiom,(
% 22.92/4.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f57,plain,(
% 22.92/4.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 22.92/4.64    inference(nnf_transformation,[],[f5])).
% 22.92/4.64  
% 22.92/4.64  fof(f70,plain,(
% 22.92/4.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f57])).
% 22.92/4.64  
% 22.92/4.64  fof(f9,axiom,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f32,plain,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 22.92/4.64    inference(ennf_transformation,[],[f9])).
% 22.92/4.64  
% 22.92/4.64  fof(f76,plain,(
% 22.92/4.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f32])).
% 22.92/4.64  
% 22.92/4.64  fof(f22,axiom,(
% 22.92/4.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f49,plain,(
% 22.92/4.64    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 22.92/4.64    inference(ennf_transformation,[],[f22])).
% 22.92/4.64  
% 22.92/4.64  fof(f50,plain,(
% 22.92/4.64    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 22.92/4.64    inference(flattening,[],[f49])).
% 22.92/4.64  
% 22.92/4.64  fof(f96,plain,(
% 22.92/4.64    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f50])).
% 22.92/4.64  
% 22.92/4.64  fof(f24,conjecture,(
% 22.92/4.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f25,negated_conjecture,(
% 22.92/4.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 22.92/4.64    inference(negated_conjecture,[],[f24])).
% 22.92/4.64  
% 22.92/4.64  fof(f53,plain,(
% 22.92/4.64    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 22.92/4.64    inference(ennf_transformation,[],[f25])).
% 22.92/4.64  
% 22.92/4.64  fof(f54,plain,(
% 22.92/4.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 22.92/4.64    inference(flattening,[],[f53])).
% 22.92/4.64  
% 22.92/4.64  fof(f61,plain,(
% 22.92/4.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 22.92/4.64    introduced(choice_axiom,[])).
% 22.92/4.64  
% 22.92/4.64  fof(f62,plain,(
% 22.92/4.64    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 22.92/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f61])).
% 22.92/4.64  
% 22.92/4.64  fof(f102,plain,(
% 22.92/4.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f69,plain,(
% 22.92/4.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f57])).
% 22.92/4.64  
% 22.92/4.64  fof(f1,axiom,(
% 22.92/4.64    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f26,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 22.92/4.64    inference(ennf_transformation,[],[f1])).
% 22.92/4.64  
% 22.92/4.64  fof(f27,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 22.92/4.64    inference(flattening,[],[f26])).
% 22.92/4.64  
% 22.92/4.64  fof(f63,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f27])).
% 22.92/4.64  
% 22.92/4.64  fof(f19,axiom,(
% 22.92/4.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f45,plain,(
% 22.92/4.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 22.92/4.64    inference(ennf_transformation,[],[f19])).
% 22.92/4.64  
% 22.92/4.64  fof(f88,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f45])).
% 22.92/4.64  
% 22.92/4.64  fof(f8,axiom,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f31,plain,(
% 22.92/4.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(ennf_transformation,[],[f8])).
% 22.92/4.64  
% 22.92/4.64  fof(f59,plain,(
% 22.92/4.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(nnf_transformation,[],[f31])).
% 22.92/4.64  
% 22.92/4.64  fof(f74,plain,(
% 22.92/4.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f59])).
% 22.92/4.64  
% 22.92/4.64  fof(f6,axiom,(
% 22.92/4.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f29,plain,(
% 22.92/4.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 22.92/4.64    inference(ennf_transformation,[],[f6])).
% 22.92/4.64  
% 22.92/4.64  fof(f71,plain,(
% 22.92/4.64    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f29])).
% 22.92/4.64  
% 22.92/4.64  fof(f10,axiom,(
% 22.92/4.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f77,plain,(
% 22.92/4.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f10])).
% 22.92/4.64  
% 22.92/4.64  fof(f13,axiom,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f37,plain,(
% 22.92/4.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(ennf_transformation,[],[f13])).
% 22.92/4.64  
% 22.92/4.64  fof(f80,plain,(
% 22.92/4.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f37])).
% 22.92/4.64  
% 22.92/4.64  fof(f23,axiom,(
% 22.92/4.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f51,plain,(
% 22.92/4.64    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 22.92/4.64    inference(ennf_transformation,[],[f23])).
% 22.92/4.64  
% 22.92/4.64  fof(f52,plain,(
% 22.92/4.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(flattening,[],[f51])).
% 22.92/4.64  
% 22.92/4.64  fof(f99,plain,(
% 22.92/4.64    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f52])).
% 22.92/4.64  
% 22.92/4.64  fof(f4,axiom,(
% 22.92/4.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f55,plain,(
% 22.92/4.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 22.92/4.64    inference(nnf_transformation,[],[f4])).
% 22.92/4.64  
% 22.92/4.64  fof(f56,plain,(
% 22.92/4.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 22.92/4.64    inference(flattening,[],[f55])).
% 22.92/4.64  
% 22.92/4.64  fof(f67,plain,(
% 22.92/4.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 22.92/4.64    inference(cnf_transformation,[],[f56])).
% 22.92/4.64  
% 22.92/4.64  fof(f107,plain,(
% 22.92/4.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 22.92/4.64    inference(equality_resolution,[],[f67])).
% 22.92/4.64  
% 22.92/4.64  fof(f100,plain,(
% 22.92/4.64    v1_funct_1(sK3)),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f18,axiom,(
% 22.92/4.64    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f43,plain,(
% 22.92/4.64    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 22.92/4.64    inference(ennf_transformation,[],[f18])).
% 22.92/4.64  
% 22.92/4.64  fof(f44,plain,(
% 22.92/4.64    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 22.92/4.64    inference(flattening,[],[f43])).
% 22.92/4.64  
% 22.92/4.64  fof(f86,plain,(
% 22.92/4.64    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f44])).
% 22.92/4.64  
% 22.92/4.64  fof(f103,plain,(
% 22.92/4.64    r1_tarski(sK2,sK0)),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f21,axiom,(
% 22.92/4.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f47,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 22.92/4.64    inference(ennf_transformation,[],[f21])).
% 22.92/4.64  
% 22.92/4.64  fof(f48,plain,(
% 22.92/4.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 22.92/4.64    inference(flattening,[],[f47])).
% 22.92/4.64  
% 22.92/4.64  fof(f60,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 22.92/4.64    inference(nnf_transformation,[],[f48])).
% 22.92/4.64  
% 22.92/4.64  fof(f90,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f60])).
% 22.92/4.64  
% 22.92/4.64  fof(f101,plain,(
% 22.92/4.64    v1_funct_2(sK3,sK0,sK1)),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f20,axiom,(
% 22.92/4.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f46,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 22.92/4.64    inference(ennf_transformation,[],[f20])).
% 22.92/4.64  
% 22.92/4.64  fof(f89,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f46])).
% 22.92/4.64  
% 22.92/4.64  fof(f16,axiom,(
% 22.92/4.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f40,plain,(
% 22.92/4.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(ennf_transformation,[],[f16])).
% 22.92/4.64  
% 22.92/4.64  fof(f41,plain,(
% 22.92/4.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(flattening,[],[f40])).
% 22.92/4.64  
% 22.92/4.64  fof(f83,plain,(
% 22.92/4.64    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f41])).
% 22.92/4.64  
% 22.92/4.64  fof(f98,plain,(
% 22.92/4.64    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f52])).
% 22.92/4.64  
% 22.92/4.64  fof(f105,plain,(
% 22.92/4.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f11,axiom,(
% 22.92/4.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f33,plain,(
% 22.92/4.64    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 22.92/4.64    inference(ennf_transformation,[],[f11])).
% 22.92/4.64  
% 22.92/4.64  fof(f34,plain,(
% 22.92/4.64    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 22.92/4.64    inference(flattening,[],[f33])).
% 22.92/4.64  
% 22.92/4.64  fof(f78,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f34])).
% 22.92/4.64  
% 22.92/4.64  fof(f87,plain,(
% 22.92/4.64    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 22.92/4.64    inference(cnf_transformation,[],[f45])).
% 22.92/4.64  
% 22.92/4.64  fof(f12,axiom,(
% 22.92/4.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f35,plain,(
% 22.92/4.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 22.92/4.64    inference(ennf_transformation,[],[f12])).
% 22.92/4.64  
% 22.92/4.64  fof(f36,plain,(
% 22.92/4.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 22.92/4.64    inference(flattening,[],[f35])).
% 22.92/4.64  
% 22.92/4.64  fof(f79,plain,(
% 22.92/4.64    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f36])).
% 22.92/4.64  
% 22.92/4.64  fof(f68,plain,(
% 22.92/4.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 22.92/4.64    inference(cnf_transformation,[],[f56])).
% 22.92/4.64  
% 22.92/4.64  fof(f106,plain,(
% 22.92/4.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 22.92/4.64    inference(equality_resolution,[],[f68])).
% 22.92/4.64  
% 22.92/4.64  fof(f104,plain,(
% 22.92/4.64    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 22.92/4.64    inference(cnf_transformation,[],[f62])).
% 22.92/4.64  
% 22.92/4.64  fof(f66,plain,(
% 22.92/4.64    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f56])).
% 22.92/4.64  
% 22.92/4.64  fof(f2,axiom,(
% 22.92/4.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 22.92/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/4.64  
% 22.92/4.64  fof(f64,plain,(
% 22.92/4.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 22.92/4.64    inference(cnf_transformation,[],[f2])).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f65]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_82743,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 22.92/4.64      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1236,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_82566,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(k2_partfun1(X2,X3,X4,X5),X6)
% 22.92/4.64      | X6 != X1
% 22.92/4.64      | k2_partfun1(X2,X3,X4,X5) != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_82568,plain,
% 22.92/4.64      ( r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 22.92/4.64      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 22.92/4.64      | k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 22.92/4.64      | k1_xboole_0 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_82566]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1235,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_82411,plain,
% 22.92/4.64      ( k1_relat_1(X0) != X1 | sK2 != X1 | sK2 = k1_relat_1(X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_82412,plain,
% 22.92/4.64      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 22.92/4.64      | sK2 = k1_relat_1(k1_xboole_0)
% 22.92/4.64      | sK2 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_82411]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_79222,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
% 22.92/4.64      | X2 != X1
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81854,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_partfun1(X0,X1,X2,X3),X4)
% 22.92/4.64      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X5)
% 22.92/4.64      | X5 != X4
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_79222]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81862,plain,
% 22.92/4.64      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 22.92/4.64      | ~ r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 22.92/4.64      | k1_xboole_0 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_81854]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_79208,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81855,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_partfun1(X0,X1,X2,X3),X4)
% 22.92/4.64      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3)
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) != X4 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_79208]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81858,plain,
% 22.92/4.64      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 22.92/4.64      | ~ r1_tarski(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_81855]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_79234,plain,
% 22.92/4.64      ( X0 != X1
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != X1
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81837,plain,
% 22.92/4.64      ( X0 != k2_partfun1(sK0,sK1,sK3,sK2)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) = X0
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_79234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81838,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 22.92/4.64      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_81837]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_18,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f81]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_81815,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_18]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1241,plain,
% 22.92/4.64      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80846,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1241]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80848,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_80846]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80809,plain,
% 22.92/4.64      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
% 22.92/4.64      | sK2 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80845,plain,
% 22.92/4.64      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
% 22.92/4.64      | sK2 != k1_relat_1(X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_80809]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80847,plain,
% 22.92/4.64      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k1_xboole_0)
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
% 22.92/4.64      | sK2 != k1_relat_1(k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_80845]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1234,plain,( X0 = X0 ),theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_80676,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1240,plain,
% 22.92/4.64      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_78540,plain,
% 22.92/4.64      ( ~ v1_relat_1(X0)
% 22.92/4.64      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1240]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_79227,plain,
% 22.92/4.64      ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_78540]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 22.92/4.64      inference(cnf_transformation,[],[f70]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_78504,plain,
% 22.92/4.64      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 22.92/4.64      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_6]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13,plain,
% 22.92/4.64      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 22.92/4.64      inference(cnf_transformation,[],[f76]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9293,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_13]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_65310,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,sK0)) | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_9293]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1237,plain,
% 22.92/4.64      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_21814,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1)
% 22.92/4.64      | sK2 != X0
% 22.92/4.64      | sK1 != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1237]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_58546,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,X0)
% 22.92/4.64      | sK2 != sK2
% 22.92/4.64      | sK1 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_21814]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_58547,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
% 22.92/4.64      | sK2 != sK2
% 22.92/4.64      | sK1 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_58546]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9088,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),X2)
% 22.92/4.64      | X2 != X1
% 22.92/4.64      | k2_relat_1(sK3) != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11706,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),X1)
% 22.92/4.64      | X1 != X0
% 22.92/4.64      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_9088]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_57886,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(sK3),X0)
% 22.92/4.64      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 22.92/4.64      | X0 != sK1
% 22.92/4.64      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_11706]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_57888,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 22.92/4.64      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 22.92/4.64      | k1_xboole_0 != sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_57886]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13725,plain,
% 22.92/4.64      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_37074,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) != X0
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) = sK1
% 22.92/4.64      | sK1 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_13725]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_56116,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,k1_xboole_0)
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) = sK1
% 22.92/4.64      | sK1 != k2_zfmisc_1(sK2,k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_37074]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1245,plain,
% 22.92/4.64      ( X0 != X1
% 22.92/4.64      | X2 != X3
% 22.92/4.64      | X4 != X5
% 22.92/4.64      | X6 != X7
% 22.92/4.64      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_50546,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,X1,X2,X3)
% 22.92/4.64      | sK2 != X3
% 22.92/4.64      | sK3 != X2
% 22.92/4.64      | sK1 != X1
% 22.92/4.64      | sK0 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1245]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_50551,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 22.92/4.64      | sK2 != k1_xboole_0
% 22.92/4.64      | sK3 != k1_xboole_0
% 22.92/4.64      | sK1 != k1_xboole_0
% 22.92/4.64      | sK0 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_50546]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_33,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 22.92/4.64      | ~ v1_funct_1(X0)
% 22.92/4.64      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 22.92/4.64      inference(cnf_transformation,[],[f96]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2514,plain,
% 22.92/4.64      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_33]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9251,plain,
% 22.92/4.64      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2514]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_50100,plain,
% 22.92/4.64      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_9251]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_40,negated_conjecture,
% 22.92/4.64      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 22.92/4.64      inference(cnf_transformation,[],[f102]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2044,plain,
% 22.92/4.64      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 22.92/4.64      inference(cnf_transformation,[],[f69]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2062,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 22.92/4.64      | r1_tarski(X0,X1) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3328,plain,
% 22.92/4.64      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2044,c_2062]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_0,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 22.92/4.64      inference(cnf_transformation,[],[f63]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2066,plain,
% 22.92/4.64      ( r1_tarski(X0,X1) != iProver_top
% 22.92/4.64      | r1_tarski(X2,X0) != iProver_top
% 22.92/4.64      | r1_tarski(X2,X1) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5130,plain,
% 22.92/4.64      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 22.92/4.64      | r1_tarski(X0,sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3328,c_2066]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2063,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 22.92/4.64      | r1_tarski(X0,X1) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_24,plain,
% 22.92/4.64      ( v5_relat_1(X0,X1)
% 22.92/4.64      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 22.92/4.64      inference(cnf_transformation,[],[f88]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_12,plain,
% 22.92/4.64      ( ~ v5_relat_1(X0,X1)
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X1)
% 22.92/4.64      | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f74]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_512,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X2)
% 22.92/4.64      | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(resolution,[status(thm)],[c_24,c_12]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2041,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4300,plain,
% 22.92/4.64      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2063,c_2041]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_12565,plain,
% 22.92/4.64      ( r1_tarski(X0,sK3) != iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),sK1) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5130,c_4300]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 22.92/4.64      | ~ v1_relat_1(X1)
% 22.92/4.64      | v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f71]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_316,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 22.92/4.64      inference(prop_impl,[status(thm)],[c_6]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_317,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 22.92/4.64      inference(renaming,[status(thm)],[c_316]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_386,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 22.92/4.64      inference(bin_hyper_res,[status(thm)],[c_8,c_317]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2042,plain,
% 22.92/4.64      ( r1_tarski(X0,X1) != iProver_top
% 22.92/4.64      | v1_relat_1(X1) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5550,plain,
% 22.92/4.64      ( r1_tarski(X0,sK3) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) = iProver_top
% 22.92/4.64      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5130,c_2042]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_14,plain,
% 22.92/4.64      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 22.92/4.64      inference(cnf_transformation,[],[f77]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2058,plain,
% 22.92/4.64      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13307,plain,
% 22.92/4.64      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 22.92/4.64      inference(forward_subsumption_resolution,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_5550,c_2058]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_14733,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(X0),sK1) = iProver_top
% 22.92/4.64      | r1_tarski(X0,sK3) != iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_12565,c_13307]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_14734,plain,
% 22.92/4.64      ( r1_tarski(X0,sK3) != iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),sK1) = iProver_top ),
% 22.92/4.64      inference(renaming,[status(thm)],[c_14733]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4831,plain,
% 22.92/4.64      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 22.92/4.64      | v1_relat_1(sK3) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3328,c_2042]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5433,plain,
% 22.92/4.64      ( v1_relat_1(sK3) = iProver_top ),
% 22.92/4.64      inference(forward_subsumption_resolution,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_4831,c_2058]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_17,plain,
% 22.92/4.64      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f80]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2055,plain,
% 22.92/4.64      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2064,plain,
% 22.92/4.64      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3492,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2055,c_2064]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5436,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5433,c_3492]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_34,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 22.92/4.64      | ~ r1_tarski(k2_relat_1(X0),X1)
% 22.92/4.64      | ~ v1_funct_1(X0)
% 22.92/4.64      | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f99]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2046,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 22.92/4.64      | v1_funct_1(X0) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5975,plain,
% 22.92/4.64      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 22.92/4.64      | v1_funct_1(X0) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2046,c_2062]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_46670,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5436,c_5975]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f107]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_46921,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 22.92/4.64      inference(light_normalisation,[status(thm)],[c_46670,c_4]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_42,negated_conjecture,
% 22.92/4.64      ( v1_funct_1(sK3) ),
% 22.92/4.64      inference(cnf_transformation,[],[f100]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_43,plain,
% 22.92/4.64      ( v1_funct_1(sK3) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22,plain,
% 22.92/4.64      ( ~ v1_funct_1(X0)
% 22.92/4.64      | v1_funct_1(k7_relat_1(X0,X1))
% 22.92/4.64      | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f86]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2409,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,X0))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_22]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2410,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 22.92/4.64      | v1_funct_1(sK3) != iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2412,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 22.92/4.64      | v1_funct_1(sK3) != iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2410]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9294,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_9293]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9296,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_9294]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_47072,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_46921,c_43,c_2412,c_5433,c_9296]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_47084,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 22.92/4.64      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_14734,c_47072]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_12075,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) != X0
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
% 22.92/4.64      | k1_xboole_0 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_37075,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,sK1) != sK1
% 22.92/4.64      | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
% 22.92/4.64      | k1_xboole_0 != sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_12075]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_39,negated_conjecture,
% 22.92/4.64      ( r1_tarski(sK2,sK0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f103]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2045,plain,
% 22.92/4.64      ( r1_tarski(sK2,sK0) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_32,plain,
% 22.92/4.64      ( ~ v1_funct_2(X0,X1,X2)
% 22.92/4.64      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 22.92/4.64      | k1_relset_1(X1,X2,X0) = X1
% 22.92/4.64      | k1_xboole_0 = X2 ),
% 22.92/4.64      inference(cnf_transformation,[],[f90]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_41,negated_conjecture,
% 22.92/4.64      ( v1_funct_2(sK3,sK0,sK1) ),
% 22.92/4.64      inference(cnf_transformation,[],[f101]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_764,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 22.92/4.64      | k1_relset_1(X1,X2,X0) = X1
% 22.92/4.64      | sK3 != X0
% 22.92/4.64      | sK1 != X2
% 22.92/4.64      | sK0 != X1
% 22.92/4.64      | k1_xboole_0 = X2 ),
% 22.92/4.64      inference(resolution_lifted,[status(thm)],[c_32,c_41]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_765,plain,
% 22.92/4.64      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 22.92/4.64      | k1_relset_1(sK0,sK1,sK3) = sK0
% 22.92/4.64      | k1_xboole_0 = sK1 ),
% 22.92/4.64      inference(unflattening,[status(thm)],[c_764]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_767,plain,
% 22.92/4.64      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_765,c_40]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_26,plain,
% 22.92/4.64      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 22.92/4.64      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f89]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2048,plain,
% 22.92/4.64      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 22.92/4.64      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3682,plain,
% 22.92/4.64      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2044,c_2048]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3821,plain,
% 22.92/4.64      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_767,c_3682]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_20,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 22.92/4.64      | ~ v1_relat_1(X1)
% 22.92/4.64      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f83]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2052,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 22.92/4.64      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5212,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 22.92/4.64      | sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(X0,sK0) != iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3821,c_2052]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8460,plain,
% 22.92/4.64      ( r1_tarski(X0,sK0) != iProver_top
% 22.92/4.64      | sK1 = k1_xboole_0
% 22.92/4.64      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_5212,c_5433]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8461,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 22.92/4.64      | sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(X0,sK0) != iProver_top ),
% 22.92/4.64      inference(renaming,[status(thm)],[c_8460]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8471,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2045,c_8461]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8555,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_8471,c_2046]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2047,plain,
% 22.92/4.64      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 22.92/4.64      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 22.92/4.64      | v1_funct_1(X2) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6254,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 22.92/4.64      | v1_funct_1(sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2044,c_2047]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6456,plain,
% 22.92/4.64      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_6254,c_43]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_35,plain,
% 22.92/4.64      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 22.92/4.64      | ~ r1_tarski(k2_relat_1(X0),X1)
% 22.92/4.64      | ~ v1_funct_1(X0)
% 22.92/4.64      | ~ v1_relat_1(X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f98]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_37,negated_conjecture,
% 22.92/4.64      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 22.92/4.64      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 22.92/4.64      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 22.92/4.64      inference(cnf_transformation,[],[f105]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_775,plain,
% 22.92/4.64      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 22.92/4.64      | ~ r1_tarski(k2_relat_1(X0),X1)
% 22.92/4.64      | ~ v1_funct_1(X0)
% 22.92/4.64      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | ~ v1_relat_1(X0)
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 22.92/4.64      | k1_relat_1(X0) != sK2
% 22.92/4.64      | sK1 != X1 ),
% 22.92/4.64      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_776,plain,
% 22.92/4.64      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 22.92/4.64      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 22.92/4.64      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 22.92/4.64      inference(unflattening,[status(thm)],[c_775]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_788,plain,
% 22.92/4.64      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 22.92/4.64      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 22.92/4.64      inference(forward_subsumption_resolution,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_776,c_512]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2032,plain,
% 22.92/4.64      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 22.92/4.64      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 22.92/4.64      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 22.92/4.64      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6462,plain,
% 22.92/4.64      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 22.92/4.64      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(demodulation,[status(thm)],[c_6456,c_2032]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_8565,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_8471,c_6462]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9762,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_8555,c_8565]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_15,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | ~ v1_relat_1(X2)
% 22.92/4.64      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f78]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2057,plain,
% 22.92/4.64      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
% 22.92/4.64      | r1_tarski(X2,X1) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6135,plain,
% 22.92/4.64      ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2045,c_2057]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6359,plain,
% 22.92/4.64      ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK2) ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5433,c_6135]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2050,plain,
% 22.92/4.64      ( v1_funct_1(X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(X0,X1)) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6515,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK0)) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_6359,c_2050]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_25,plain,
% 22.92/4.64      ( v4_relat_1(X0,X1)
% 22.92/4.64      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 22.92/4.64      inference(cnf_transformation,[],[f87]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2049,plain,
% 22.92/4.64      ( v4_relat_1(X0,X1) = iProver_top
% 22.92/4.64      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3606,plain,
% 22.92/4.64      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2044,c_2049]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_16,plain,
% 22.92/4.64      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f79]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2056,plain,
% 22.92/4.64      ( k7_relat_1(X0,X1) = X0
% 22.92/4.64      | v4_relat_1(X0,X1) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4497,plain,
% 22.92/4.64      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3606,c_2056]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1243,plain,
% 22.92/4.64      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 22.92/4.64      theory(equality) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2431,plain,
% 22.92/4.64      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1243]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3739,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,X0))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | k7_relat_1(sK3,X0) != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2431]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11036,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK0))
% 22.92/4.64      | ~ v1_funct_1(sK3)
% 22.92/4.64      | k7_relat_1(sK3,sK0) != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3739]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11037,plain,
% 22.92/4.64      ( k7_relat_1(sK3,sK0) != sK3
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,sK0)) = iProver_top
% 22.92/4.64      | v1_funct_1(sK3) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_11036]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22002,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_6515,c_43,c_4497,c_5433,c_11037]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5439,plain,
% 22.92/4.64      ( k7_relat_1(sK3,sK0) = sK3 ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_5433,c_4497]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22006,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(light_normalisation,[status(thm)],[c_22002,c_5439]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22009,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top ),
% 22.92/4.64      inference(forward_subsumption_resolution,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_22006,c_5433]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_35660,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 22.92/4.64      | sK1 = k1_xboole_0
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_9762,c_22009]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_35661,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(renaming,[status(thm)],[c_35660]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_35669,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_14734,c_35661]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_35692,plain,
% 22.92/4.64      ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 22.92/4.64      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 22.92/4.64      | sK1 = k1_xboole_0 ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_35669]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3,plain,
% 22.92/4.64      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f106]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5972,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(sK3) != iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3821,c_2046]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9628,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_5972,c_43,c_5433]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9638,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(sK0,X0)) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_9628,c_2062]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_30581,plain,
% 22.92/4.64      ( sK1 = k1_xboole_0
% 22.92/4.64      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3,c_9638]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_38,negated_conjecture,
% 22.92/4.64      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 22.92/4.64      inference(cnf_transformation,[],[f104]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5,plain,
% 22.92/4.64      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 22.92/4.64      | k1_xboole_0 = X0
% 22.92/4.64      | k1_xboole_0 = X1 ),
% 22.92/4.64      inference(cnf_transformation,[],[f66]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_137,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 22.92/4.64      | k1_xboole_0 = k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_5]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_138,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_4]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_1,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,X0) ),
% 22.92/4.64      inference(cnf_transformation,[],[f64]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_142,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_144,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_142]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3369,plain,
% 22.92/4.64      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3370,plain,
% 22.92/4.64      ( sK1 != k1_xboole_0
% 22.92/4.64      | k1_xboole_0 = sK1
% 22.92/4.64      | k1_xboole_0 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3369]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3423,plain,
% 22.92/4.64      ( sK3 = sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2684,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,k1_xboole_0)
% 22.92/4.64      | ~ r1_tarski(sK3,X0)
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_0]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3844,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0)
% 22.92/4.64      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2684]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3849,plain,
% 22.92/4.64      ( r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3851,plain,
% 22.92/4.64      ( r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3849]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6573,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(k2_zfmisc_1(X2,X3),k1_xboole_0)
% 22.92/4.64      | k2_zfmisc_1(X2,X3) != X0
% 22.92/4.64      | k1_xboole_0 != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6574,plain,
% 22.92/4.64      ( k2_zfmisc_1(X0,X1) != X2
% 22.92/4.64      | k1_xboole_0 != X3
% 22.92/4.64      | r1_tarski(X2,X3) != iProver_top
% 22.92/4.64      | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_6573]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6576,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 22.92/4.64      | k1_xboole_0 != k1_xboole_0
% 22.92/4.64      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 22.92/4.64      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_6574]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2741,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 22.92/4.64      | X2 != X0
% 22.92/4.64      | k2_zfmisc_1(X3,X4) != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4889,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(X2,X3))
% 22.92/4.64      | k2_zfmisc_1(X2,X3) != X1
% 22.92/4.64      | sK3 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2741]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5922,plain,
% 22.92/4.64      ( ~ r1_tarski(sK3,X0)
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(X1,X2))
% 22.92/4.64      | k2_zfmisc_1(X1,X2) != X0
% 22.92/4.64      | sK3 != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_4889]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_10183,plain,
% 22.92/4.64      ( r1_tarski(sK3,k2_zfmisc_1(X0,X1))
% 22.92/4.64      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 22.92/4.64      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
% 22.92/4.64      | sK3 != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_5922]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_10184,plain,
% 22.92/4.64      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
% 22.92/4.64      | sK3 != sK3
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_10183]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_10186,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
% 22.92/4.64      | sK3 != sK3
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_10184]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11618,plain,
% 22.92/4.64      ( X0 != sK1
% 22.92/4.64      | X1 != sK0
% 22.92/4.64      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1237]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11619,plain,
% 22.92/4.64      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
% 22.92/4.64      | k1_xboole_0 != sK1
% 22.92/4.64      | k1_xboole_0 != sK0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_11618]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_31895,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_30581,c_38,c_137,c_138,c_144,c_3328,c_3370,c_3423,
% 22.92/4.64                 c_3851,c_6576,c_10186,c_11619]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_31897,plain,
% 22.92/4.64      ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 22.92/4.64      | r1_tarski(sK3,k1_xboole_0) ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_31895]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_24637,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_18]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_24642,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_24637]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_24644,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_24642]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2522,plain,
% 22.92/4.64      ( v1_funct_1(X0)
% 22.92/4.64      | ~ v1_funct_1(k7_relat_1(sK3,X1))
% 22.92/4.64      | X0 != k7_relat_1(sK3,X1) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1243]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_10970,plain,
% 22.92/4.64      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 22.92/4.64      | ~ v1_funct_1(k7_relat_1(sK3,X0))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2522]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22239,plain,
% 22.92/4.64      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 22.92/4.64      | ~ v1_funct_1(k7_relat_1(sK3,sK2))
% 22.92/4.64      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_10970]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_22010,plain,
% 22.92/4.64      ( v1_funct_1(k7_relat_1(sK3,sK2)) ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_22009]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3475,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,X1)
% 22.92/4.64      | r1_tarski(sK2,k1_xboole_0)
% 22.92/4.64      | sK2 != X0
% 22.92/4.64      | k1_xboole_0 != X1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1236]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7116,plain,
% 22.92/4.64      ( ~ r1_tarski(sK2,X0)
% 22.92/4.64      | r1_tarski(sK2,k1_xboole_0)
% 22.92/4.64      | sK2 != sK2
% 22.92/4.64      | k1_xboole_0 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3475]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13961,plain,
% 22.92/4.64      ( ~ r1_tarski(sK2,sK0)
% 22.92/4.64      | r1_tarski(sK2,k1_xboole_0)
% 22.92/4.64      | sK2 != sK2
% 22.92/4.64      | k1_xboole_0 != sK0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_7116]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5473,plain,
% 22.92/4.64      ( X0 != X1
% 22.92/4.64      | k2_zfmisc_1(sK2,k1_xboole_0) != X1
% 22.92/4.64      | k2_zfmisc_1(sK2,k1_xboole_0) = X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13732,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
% 22.92/4.64      | k2_zfmisc_1(sK2,k1_xboole_0) = sK1
% 22.92/4.64      | sK1 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_5473]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13733,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,k1_xboole_0) = sK1
% 22.92/4.64      | k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
% 22.92/4.64      | sK1 != k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_13732]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2577,plain,
% 22.92/4.64      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3352,plain,
% 22.92/4.64      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2577]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_13731,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,k1_xboole_0) != sK1
% 22.92/4.64      | sK1 = k2_zfmisc_1(sK2,k1_xboole_0)
% 22.92/4.64      | sK1 != sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3352]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_11707,plain,
% 22.92/4.64      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9172,plain,
% 22.92/4.64      ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
% 22.92/4.64      | k1_xboole_0 = k7_relat_1(sK3,X0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9175,plain,
% 22.92/4.64      ( k1_xboole_0 = k7_relat_1(sK3,X0)
% 22.92/4.64      | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_9172]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_9177,plain,
% 22.92/4.64      ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
% 22.92/4.64      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_9175]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2054,plain,
% 22.92/4.64      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 22.92/4.64      | v1_relat_1(X0) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3321,plain,
% 22.92/4.64      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 22.92/4.64      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2054,c_2064]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_112,plain,
% 22.92/4.64      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_114,plain,
% 22.92/4.64      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_112]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2414,plain,
% 22.92/4.64      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 22.92/4.64      | v1_relat_1(X0)
% 22.92/4.64      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_386]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2415,plain,
% 22.92/4.64      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 22.92/4.64      | v1_relat_1(X0) = iProver_top
% 22.92/4.64      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2417,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2415]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2734,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2737,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_2734]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2739,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2737]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3428,plain,
% 22.92/4.64      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_3321,c_114,c_2417,c_2739]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3491,plain,
% 22.92/4.64      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 22.92/4.64      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3428,c_2055]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3560,plain,
% 22.92/4.64      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_3491,c_114,c_2417,c_2739]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_3567,plain,
% 22.92/4.64      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3560,c_2064]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5971,plain,
% 22.92/4.64      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k1_xboole_0) != iProver_top
% 22.92/4.64      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3567,c_2046]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6035,plain,
% 22.92/4.64      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 22.92/4.64      | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
% 22.92/4.64      | v1_funct_1(k1_xboole_0) != iProver_top
% 22.92/4.64      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(light_normalisation,[status(thm)],[c_5971,c_4]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_134,plain,
% 22.92/4.64      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 22.92/4.64      | r1_tarski(X0,X1) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_136,plain,
% 22.92/4.64      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 22.92/4.64      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_134]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7223,plain,
% 22.92/4.64      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 22.92/4.64      inference(global_propositional_subsumption,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_6035,c_136,c_144]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6255,plain,
% 22.92/4.64      ( k2_partfun1(X0,k1_xboole_0,X1,X2) = k7_relat_1(X1,X2)
% 22.92/4.64      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_funct_1(X1) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_3,c_2047]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7230,plain,
% 22.92/4.64      ( k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1) = k7_relat_1(k1_xboole_0,X1)
% 22.92/4.64      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_7223,c_6255]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7247,plain,
% 22.92/4.64      ( k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0
% 22.92/4.64      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(demodulation,[status(thm)],[c_7230,c_3428]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_7261,plain,
% 22.92/4.64      ( k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 22.92/4.64      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_7247]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2059,plain,
% 22.92/4.64      ( v1_relat_1(X0) != iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6519,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 22.92/4.64      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_6359,c_2059]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_6551,plain,
% 22.92/4.64      ( v1_relat_1(k7_relat_1(sK3,sK2))
% 22.92/4.64      | ~ v1_relat_1(k7_relat_1(sK3,sK0)) ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_6519]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2713,plain,
% 22.92/4.64      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5960,plain,
% 22.92/4.64      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2713]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5962,plain,
% 22.92/4.64      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_5960]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5471,plain,
% 22.92/4.64      ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_3]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_5434,plain,
% 22.92/4.64      ( v1_relat_1(sK3) ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_5433]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4301,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 22.92/4.64      | v1_relat_1(sK3) != iProver_top ),
% 22.92/4.64      inference(superposition,[status(thm)],[c_2044,c_2041]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_4323,plain,
% 22.92/4.64      ( r1_tarski(k2_relat_1(sK3),sK1) | ~ v1_relat_1(sK3) ),
% 22.92/4.64      inference(predicate_to_equality_rev,[status(thm)],[c_4301]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2758,plain,
% 22.92/4.64      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2582,plain,
% 22.92/4.64      ( sK0 = sK0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2480,plain,
% 22.92/4.64      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2581,plain,
% 22.92/4.64      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2480]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2579,plain,
% 22.92/4.64      ( sK2 = sK2 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2479,plain,
% 22.92/4.64      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1235]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2578,plain,
% 22.92/4.64      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2479]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2576,plain,
% 22.92/4.64      ( sK1 = sK1 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1234]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2547,plain,
% 22.92/4.64      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2528,plain,
% 22.92/4.64      ( X0 != k7_relat_1(sK3,X1)
% 22.92/4.64      | v1_funct_1(X0) = iProver_top
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
% 22.92/4.64      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_2530,plain,
% 22.92/4.64      ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
% 22.92/4.64      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 22.92/4.64      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_2528]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(c_143,plain,
% 22.92/4.64      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 22.92/4.64      inference(instantiation,[status(thm)],[c_1]) ).
% 22.92/4.64  
% 22.92/4.64  cnf(contradiction,plain,
% 22.92/4.64      ( $false ),
% 22.92/4.64      inference(minisat,
% 22.92/4.64                [status(thm)],
% 22.92/4.64                [c_82743,c_82568,c_82412,c_81862,c_81858,c_81838,c_81815,
% 22.92/4.64                 c_80848,c_80847,c_80676,c_79227,c_78504,c_65310,c_58547,
% 22.92/4.64                 c_57888,c_56116,c_50551,c_50100,c_47084,c_37075,c_35692,
% 22.92/4.64                 c_31897,c_24644,c_22239,c_22010,c_13961,c_13733,c_13731,
% 22.92/4.64                 c_11707,c_9177,c_7261,c_6551,c_5962,c_5471,c_5434,
% 22.92/4.64                 c_5433,c_4323,c_3567,c_3423,c_3370,c_2758,c_2582,c_2581,
% 22.92/4.64                 c_2579,c_2578,c_2576,c_2547,c_2530,c_2412,c_788,c_143,
% 22.92/4.64                 c_138,c_137,c_38,c_39,c_40,c_43,c_42]) ).
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  % SZS output end CNFRefutation for theBenchmark.p
% 22.92/4.64  
% 22.92/4.64  ------                               Statistics
% 22.92/4.64  
% 22.92/4.64  ------ General
% 22.92/4.64  
% 22.92/4.64  abstr_ref_over_cycles:                  0
% 22.92/4.64  abstr_ref_under_cycles:                 0
% 22.92/4.64  gc_basic_clause_elim:                   0
% 22.92/4.64  forced_gc_time:                         0
% 22.92/4.64  parsing_time:                           0.014
% 22.92/4.64  unif_index_cands_time:                  0.
% 22.92/4.64  unif_index_add_time:                    0.
% 22.92/4.64  orderings_time:                         0.
% 22.92/4.64  out_proof_time:                         0.038
% 22.92/4.64  total_time:                             3.703
% 22.92/4.64  num_of_symbols:                         50
% 22.92/4.64  num_of_terms:                           61331
% 22.92/4.64  
% 22.92/4.64  ------ Preprocessing
% 22.92/4.64  
% 22.92/4.64  num_of_splits:                          0
% 22.92/4.64  num_of_split_atoms:                     0
% 22.92/4.64  num_of_reused_defs:                     0
% 22.92/4.64  num_eq_ax_congr_red:                    13
% 22.92/4.64  num_of_sem_filtered_clauses:            1
% 22.92/4.64  num_of_subtypes:                        0
% 22.92/4.64  monotx_restored_types:                  0
% 22.92/4.64  sat_num_of_epr_types:                   0
% 22.92/4.64  sat_num_of_non_cyclic_types:            0
% 22.92/4.64  sat_guarded_non_collapsed_types:        0
% 22.92/4.64  num_pure_diseq_elim:                    0
% 22.92/4.64  simp_replaced_by:                       0
% 22.92/4.64  res_preprocessed:                       189
% 22.92/4.64  prep_upred:                             0
% 22.92/4.64  prep_unflattend:                        43
% 22.92/4.64  smt_new_axioms:                         0
% 22.92/4.64  pred_elim_cands:                        5
% 22.92/4.64  pred_elim:                              2
% 22.92/4.64  pred_elim_cl:                           0
% 22.92/4.64  pred_elim_cycles:                       5
% 22.92/4.64  merged_defs:                            8
% 22.92/4.64  merged_defs_ncl:                        0
% 22.92/4.64  bin_hyper_res:                          9
% 22.92/4.64  prep_cycles:                            4
% 22.92/4.64  pred_elim_time:                         0.01
% 22.92/4.64  splitting_time:                         0.
% 22.92/4.64  sem_filter_time:                        0.
% 22.92/4.64  monotx_time:                            0.001
% 22.92/4.64  subtype_inf_time:                       0.
% 22.92/4.64  
% 22.92/4.64  ------ Problem properties
% 22.92/4.64  
% 22.92/4.64  clauses:                                41
% 22.92/4.64  conjectures:                            4
% 22.92/4.64  epr:                                    7
% 22.92/4.64  horn:                                   36
% 22.92/4.64  ground:                                 12
% 22.92/4.64  unary:                                  7
% 22.92/4.64  binary:                                 12
% 22.92/4.64  lits:                                   113
% 22.92/4.64  lits_eq:                                37
% 22.92/4.64  fd_pure:                                0
% 22.92/4.64  fd_pseudo:                              0
% 22.92/4.64  fd_cond:                                4
% 22.92/4.64  fd_pseudo_cond:                         0
% 22.92/4.64  ac_symbols:                             0
% 22.92/4.64  
% 22.92/4.64  ------ Propositional Solver
% 22.92/4.64  
% 22.92/4.64  prop_solver_calls:                      36
% 22.92/4.64  prop_fast_solver_calls:                 3112
% 22.92/4.64  smt_solver_calls:                       0
% 22.92/4.64  smt_fast_solver_calls:                  0
% 22.92/4.64  prop_num_of_clauses:                    27018
% 22.92/4.64  prop_preprocess_simplified:             34742
% 22.92/4.64  prop_fo_subsumed:                       145
% 22.92/4.64  prop_solver_time:                       0.
% 22.92/4.64  smt_solver_time:                        0.
% 22.92/4.64  smt_fast_solver_time:                   0.
% 22.92/4.64  prop_fast_solver_time:                  0.
% 22.92/4.64  prop_unsat_core_time:                   0.004
% 22.92/4.64  
% 22.92/4.64  ------ QBF
% 22.92/4.64  
% 22.92/4.64  qbf_q_res:                              0
% 22.92/4.64  qbf_num_tautologies:                    0
% 22.92/4.64  qbf_prep_cycles:                        0
% 22.92/4.64  
% 22.92/4.64  ------ BMC1
% 22.92/4.64  
% 22.92/4.64  bmc1_current_bound:                     -1
% 22.92/4.64  bmc1_last_solved_bound:                 -1
% 22.92/4.64  bmc1_unsat_core_size:                   -1
% 22.92/4.64  bmc1_unsat_core_parents_size:           -1
% 22.92/4.64  bmc1_merge_next_fun:                    0
% 22.92/4.64  bmc1_unsat_core_clauses_time:           0.
% 22.92/4.64  
% 22.92/4.64  ------ Instantiation
% 22.92/4.64  
% 22.92/4.64  inst_num_of_clauses:                    197
% 22.92/4.64  inst_num_in_passive:                    23
% 22.92/4.64  inst_num_in_active:                     2071
% 22.92/4.64  inst_num_in_unprocessed:                43
% 22.92/4.64  inst_num_of_loops:                      3144
% 22.92/4.64  inst_num_of_learning_restarts:          1
% 22.92/4.64  inst_num_moves_active_passive:          1066
% 22.92/4.64  inst_lit_activity:                      0
% 22.92/4.64  inst_lit_activity_moves:                0
% 22.92/4.64  inst_num_tautologies:                   0
% 22.92/4.64  inst_num_prop_implied:                  0
% 22.92/4.64  inst_num_existing_simplified:           0
% 22.92/4.64  inst_num_eq_res_simplified:             0
% 22.92/4.64  inst_num_child_elim:                    0
% 22.92/4.64  inst_num_of_dismatching_blockings:      4214
% 22.92/4.64  inst_num_of_non_proper_insts:           6746
% 22.92/4.64  inst_num_of_duplicates:                 0
% 22.92/4.64  inst_inst_num_from_inst_to_res:         0
% 22.92/4.64  inst_dismatching_checking_time:         0.
% 22.92/4.64  
% 22.92/4.64  ------ Resolution
% 22.92/4.64  
% 22.92/4.64  res_num_of_clauses:                     53
% 22.92/4.64  res_num_in_passive:                     53
% 22.92/4.64  res_num_in_active:                      0
% 22.92/4.64  res_num_of_loops:                       193
% 22.92/4.64  res_forward_subset_subsumed:            105
% 22.92/4.64  res_backward_subset_subsumed:           2
% 22.92/4.64  res_forward_subsumed:                   0
% 22.92/4.64  res_backward_subsumed:                  0
% 22.92/4.64  res_forward_subsumption_resolution:     3
% 22.92/4.64  res_backward_subsumption_resolution:    0
% 22.92/4.64  res_clause_to_clause_subsumption:       18660
% 22.92/4.64  res_orphan_elimination:                 0
% 22.92/4.64  res_tautology_del:                      396
% 22.92/4.64  res_num_eq_res_simplified:              1
% 22.92/4.64  res_num_sel_changes:                    0
% 22.92/4.64  res_moves_from_active_to_pass:          0
% 22.92/4.64  
% 22.92/4.64  ------ Superposition
% 22.92/4.64  
% 22.92/4.64  sup_time_total:                         0.
% 22.92/4.64  sup_time_generating:                    0.
% 22.92/4.64  sup_time_sim_full:                      0.
% 22.92/4.64  sup_time_sim_immed:                     0.
% 22.92/4.64  
% 22.92/4.64  sup_num_of_clauses:                     3250
% 22.92/4.64  sup_num_in_active:                      599
% 22.92/4.64  sup_num_in_passive:                     2651
% 22.92/4.64  sup_num_of_loops:                       628
% 22.92/4.64  sup_fw_superposition:                   3202
% 22.92/4.64  sup_bw_superposition:                   2261
% 22.92/4.64  sup_immediate_simplified:               1732
% 22.92/4.64  sup_given_eliminated:                   4
% 22.92/4.64  comparisons_done:                       0
% 22.92/4.64  comparisons_avoided:                    109
% 22.92/4.64  
% 22.92/4.64  ------ Simplifications
% 22.92/4.64  
% 22.92/4.64  
% 22.92/4.64  sim_fw_subset_subsumed:                 245
% 22.92/4.64  sim_bw_subset_subsumed:                 45
% 22.92/4.64  sim_fw_subsumed:                        783
% 22.92/4.64  sim_bw_subsumed:                        30
% 22.92/4.64  sim_fw_subsumption_res:                 16
% 22.92/4.64  sim_bw_subsumption_res:                 0
% 22.92/4.64  sim_tautology_del:                      173
% 22.92/4.64  sim_eq_tautology_del:                   224
% 22.92/4.64  sim_eq_res_simp:                        0
% 22.92/4.64  sim_fw_demodulated:                     475
% 22.92/4.64  sim_bw_demodulated:                     33
% 22.92/4.64  sim_light_normalised:                   586
% 22.92/4.64  sim_joinable_taut:                      0
% 22.92/4.64  sim_joinable_simp:                      0
% 22.92/4.64  sim_ac_normalised:                      0
% 22.92/4.64  sim_smt_subsumption:                    0
% 22.92/4.64  
%------------------------------------------------------------------------------
