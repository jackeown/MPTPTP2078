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
% DateTime   : Thu Dec  3 12:09:31 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 549 expanded)
%              Number of clauses        :   96 ( 204 expanded)
%              Number of leaves         :   23 ( 123 expanded)
%              Depth                    :   23
%              Number of atoms          :  531 (2914 expanded)
%              Number of equality atoms :  173 ( 295 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
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

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f70,plain,(
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
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK6,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK6,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK6,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK6,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK6,X0,X3)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
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
          ( ( ~ m1_subset_1(k2_partfun1(sK2,sK5,X4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
            | ~ v1_funct_2(k2_partfun1(sK2,sK5,X4,sK3),sK3,sK4)
            | ~ v1_funct_1(k2_partfun1(sK2,sK5,X4,sK3)) )
          & r1_tarski(k7_relset_1(sK2,sK5,X4,sK3),sK4)
          & r1_tarski(sK3,sK2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
          & v1_funct_2(X4,sK2,sK5)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4)
      | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) )
    & r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4)
    & r1_tarski(sK3,sK2)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
    & v1_funct_2(sK6,sK2,sK5)
    & v1_funct_1(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f57,f70,f69])).

fof(f118,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) ),
    inference(cnf_transformation,[],[f71])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4)
    | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) ),
    inference(cnf_transformation,[],[f71])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f22,axiom,(
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
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    v1_funct_2(sK6,sK2,sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f64])).

fof(f80,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2483,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2487,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5554,plain,
    ( k2_partfun1(sK2,sK5,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_2487])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_51,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_6080,plain,
    ( k2_partfun1(sK2,sK5,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5554,c_51])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6143,plain,
    ( m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6080,c_2489])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_6359,plain,
    ( m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6143,c_51,c_53])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6366,plain,
    ( r1_tarski(k7_relat_1(sK6,X0),k2_zfmisc_1(sK2,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6359,c_2499])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_365,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_446,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_366])).

cnf(c_2478,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_7771,plain,
    ( v1_relat_1(k7_relat_1(sK6,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6366,c_2478])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2498,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12779,plain,
    ( v1_relat_1(k7_relat_1(sK6,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7771,c_2498])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4)
    | ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_921,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK2,sK5,sK6,sK3) != X0
    | k1_relat_1(X0) != sK3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_43])).

cnf(c_922,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)),sK4)
    | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | ~ v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3 ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_934,plain,
    ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | ~ v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_922,c_622])).

cnf(c_2463,plain,
    ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top
    | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_939,plain,
    ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top
    | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3025,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK6,X2))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_3186,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
    | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3025])).

cnf(c_3187,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) != iProver_top
    | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_3387,plain,
    ( m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
    | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_51,c_53,c_939,c_3187])).

cnf(c_3388,plain,
    ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3387])).

cnf(c_6084,plain,
    ( k1_relat_1(k7_relat_1(sK6,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6080,c_3388])).

cnf(c_45,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2484,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK6,sK2,sK5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_47])).

cnf(c_769,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
    | k1_relset_1(sK2,sK5,sK6) = sK2
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_771,plain,
    ( k1_relset_1(sK2,sK5,sK6) = sK2
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_46])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2492,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4110,plain,
    ( k1_relset_1(sK2,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2483,c_2492])).

cnf(c_4249,plain,
    ( k1_relat_1(sK6) = sK2
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_771,c_4110])).

cnf(c_49,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_366])).

cnf(c_2906,plain,
    ( ~ r1_tarski(X0,sK1(X1))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1)) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_3626,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1(X0))
    | ~ v1_xboole_0(sK1(X0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2906])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3627,plain,
    ( r1_tarski(k1_xboole_0,sK1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1447,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4053,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_4055,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4053])).

cnf(c_4324,plain,
    ( k1_relat_1(sK6) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_49,c_7,c_3626,c_3627,c_4055])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2495,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4729,plain,
    ( k1_relat_1(k7_relat_1(sK6,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4324,c_2495])).

cnf(c_3447,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK2,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_2499])).

cnf(c_3948,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_2478])).

cnf(c_4089,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3948,c_2498])).

cnf(c_5141,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | k1_relat_1(k7_relat_1(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4729,c_4089])).

cnf(c_5142,plain,
    ( k1_relat_1(k7_relat_1(sK6,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5141])).

cnf(c_5152,plain,
    ( k1_relat_1(k7_relat_1(sK6,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2484,c_5142])).

cnf(c_6131,plain,
    ( sK3 != sK3
    | m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6084,c_5152])).

cnf(c_6132,plain,
    ( m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6131])).

cnf(c_9039,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK6,sK3)),sK3) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK6,sK3)),sK4) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_6132])).

cnf(c_9043,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK6,sK3)),sK4) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9039,c_5152])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2497,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4091,plain,
    ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_4089,c_2497])).

cnf(c_9044,plain,
    ( r1_tarski(k9_relat_1(sK6,sK3),sK4) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9043,c_4091])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2491,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4213,plain,
    ( k7_relset_1(sK2,sK5,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_2483,c_2491])).

cnf(c_44,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2485,plain,
    ( r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4253,plain,
    ( r1_tarski(k9_relat_1(sK6,sK3),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4213,c_2485])).

cnf(c_11877,plain,
    ( r1_tarski(sK3,sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9044,c_4253])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2504,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11883,plain,
    ( v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11877,c_2504])).

cnf(c_12788,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12779,c_11883])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 48
% 3.45/0.99  conjectures                             5
% 3.45/0.99  EPR                                     11
% 3.45/0.99  Horn                                    40
% 3.45/0.99  unary                                   10
% 3.45/0.99  binary                                  10
% 3.45/0.99  lits                                    142
% 3.45/0.99  lits eq                                 34
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 3
% 3.45/0.99  fd_pseudo_cond                          1
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Schedule dynamic 5 is on 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     none
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       false
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99   Resolution empty clause
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f26,conjecture,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f27,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 3.45/0.99    inference(negated_conjecture,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 3.45/0.99    inference(ennf_transformation,[],[f27])).
% 3.45/0.99  
% 3.45/0.99  fof(f57,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 3.45/0.99    inference(flattening,[],[f56])).
% 3.45/0.99  
% 3.45/0.99  fof(f70,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK6,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK6,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK6,X1))) & r1_tarski(k7_relset_1(X0,X3,sK6,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK6,X0,X3) & v1_funct_1(sK6))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f69,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK2,sK5,X4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(k2_partfun1(sK2,sK5,X4,sK3),sK3,sK4) | ~v1_funct_1(k2_partfun1(sK2,sK5,X4,sK3))) & r1_tarski(k7_relset_1(sK2,sK5,X4,sK3),sK4) & r1_tarski(sK3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) & v1_funct_2(X4,sK2,sK5) & v1_funct_1(X4)) & ~v1_xboole_0(sK5))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f71,plain,(
% 3.45/0.99    ((~m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4) | ~v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))) & r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) & r1_tarski(sK3,sK2) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) & v1_funct_2(sK6,sK2,sK5) & v1_funct_1(sK6)) & ~v1_xboole_0(sK5)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f57,f70,f69])).
% 3.45/0.99  
% 3.45/0.99  fof(f118,plain,(
% 3.45/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f24,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f52,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.45/0.99    inference(ennf_transformation,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.45/0.99    inference(flattening,[],[f52])).
% 3.45/0.99  
% 3.45/0.99  fof(f111,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f53])).
% 3.45/0.99  
% 3.45/0.99  fof(f116,plain,(
% 3.45/0.99    v1_funct_1(sK6)),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f50,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.45/0.99    inference(ennf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f51,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.45/0.99    inference(flattening,[],[f50])).
% 3.45/0.99  
% 3.45/0.99  fof(f110,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f51])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f66,plain,(
% 3.45/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f82,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f66])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f85,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f31])).
% 3.45/0.99  
% 3.45/0.99  fof(f83,plain,(
% 3.45/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f66])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,axiom,(
% 3.45/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f88,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f20,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(ennf_transformation,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f45,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(flattening,[],[f44])).
% 3.45/0.99  
% 3.45/0.99  fof(f99,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f25,axiom,(
% 3.45/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.45/0.99    inference(ennf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(flattening,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f113,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f55])).
% 3.45/0.99  
% 3.45/0.99  fof(f121,plain,(
% 3.45/0.99    ~m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4) | ~v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f15,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f94,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f39])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f67,plain,(
% 3.45/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(nnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f86,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f67])).
% 3.45/0.99  
% 3.45/0.99  fof(f109,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f51])).
% 3.45/0.99  
% 3.45/0.99  fof(f119,plain,(
% 3.45/0.99    r1_tarski(sK3,sK2)),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f49,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(flattening,[],[f48])).
% 3.45/0.99  
% 3.45/0.99  fof(f68,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f103,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f68])).
% 3.45/0.99  
% 3.45/0.99  fof(f117,plain,(
% 3.45/0.99    v1_funct_2(sK6,sK2,sK5)),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f18,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f42,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f97,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f42])).
% 3.45/0.99  
% 3.45/0.99  fof(f115,plain,(
% 3.45/0.99    ~v1_xboole_0(sK5)),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f64,plain,(
% 3.45/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f65,plain,(
% 3.45/0.99    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f64])).
% 3.45/0.99  
% 3.45/0.99  fof(f80,plain,(
% 3.45/0.99    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f65])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f81,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f29])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f78,plain,(
% 3.45/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f14,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(flattening,[],[f37])).
% 3.45/0.99  
% 3.45/0.99  fof(f92,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f38])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f89,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f19,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f43,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f98,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f120,plain,(
% 3.45/0.99    r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4)),
% 3.45/0.99    inference(cnf_transformation,[],[f71])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f62,plain,(
% 3.45/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/0.99    inference(nnf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f63,plain,(
% 3.45/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/0.99    inference(flattening,[],[f62])).
% 3.45/0.99  
% 3.45/0.99  fof(f75,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f123,plain,(
% 3.45/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.45/0.99    inference(equality_resolution,[],[f75])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_46,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2483,plain,
% 3.45/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_39,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | ~ v1_funct_1(X0)
% 3.45/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2487,plain,
% 3.45/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.45/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5554,plain,
% 3.45/0.99      ( k2_partfun1(sK2,sK5,sK6,X0) = k7_relat_1(sK6,X0)
% 3.45/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2483,c_2487]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_48,negated_conjecture,
% 3.45/0.99      ( v1_funct_1(sK6) ),
% 3.45/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_51,plain,
% 3.45/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6080,plain,
% 3.45/0.99      ( k2_partfun1(sK2,sK5,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5554,c_51]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_37,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | ~ v1_funct_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2489,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.45/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6143,plain,
% 3.45/0.99      ( m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top
% 3.45/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) != iProver_top
% 3.45/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_6080,c_2489]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_53,plain,
% 3.45/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6359,plain,
% 3.45/0.99      ( m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_6143,c_51,c_53]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_11,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2499,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.45/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6366,plain,
% 3.45/0.99      ( r1_tarski(k7_relat_1(sK6,X0),k2_zfmisc_1(sK2,sK5)) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_6359,c_2499]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_10,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_365,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.45/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_366,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_365]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_446,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.45/0.99      inference(bin_hyper_res,[status(thm)],[c_13,c_366]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2478,plain,
% 3.45/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7771,plain,
% 3.45/0.99      ( v1_relat_1(k7_relat_1(sK6,X0)) = iProver_top
% 3.45/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK5)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_6366,c_2478]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2498,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12779,plain,
% 3.45/0.99      ( v1_relat_1(k7_relat_1(sK6,X0)) = iProver_top ),
% 3.45/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7771,c_2498]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_27,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.45/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.45/0.99      | ~ v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2490,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.45/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.45/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_41,plain,
% 3.45/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.45/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.45/0.99      | ~ v1_funct_1(X0)
% 3.45/0.99      | ~ v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_43,negated_conjecture,
% 3.45/0.99      ( ~ v1_funct_2(k2_partfun1(sK2,sK5,sK6,sK3),sK3,sK4)
% 3.45/0.99      | ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.45/0.99      | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_921,plain,
% 3.45/0.99      ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.45/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.45/0.99      | ~ v1_funct_1(X0)
% 3.45/0.99      | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | ~ v1_relat_1(X0)
% 3.45/0.99      | k2_partfun1(sK2,sK5,sK6,sK3) != X0
% 3.45/0.99      | k1_relat_1(X0) != sK3
% 3.45/0.99      | sK4 != X1 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_41,c_43]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_922,plain,
% 3.45/0.99      ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.45/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)),sK4)
% 3.45/0.99      | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | ~ v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3 ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_921]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_21,plain,
% 3.45/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_15,plain,
% 3.45/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_622,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.45/0.99      | ~ v1_relat_1(X0) ),
% 3.45/0.99      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_934,plain,
% 3.45/0.99      ( ~ m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.45/0.99      | ~ v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | ~ v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3 ),
% 3.45/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_922,c_622]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2463,plain,
% 3.45/0.99      ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
% 3.45/0.99      | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top
% 3.45/0.99      | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_939,plain,
% 3.45/0.99      ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
% 3.45/0.99      | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top
% 3.45/0.99      | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_38,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | ~ v1_funct_1(X0)
% 3.45/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3025,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK6,X2))
% 3.45/0.99      | ~ v1_funct_1(sK6) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3186,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
% 3.45/0.99      | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3))
% 3.45/0.99      | ~ v1_funct_1(sK6) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_3025]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3187,plain,
% 3.45/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5))) != iProver_top
% 3.45/0.99      | v1_funct_1(k2_partfun1(sK2,sK5,sK6,sK3)) = iProver_top
% 3.45/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3387,plain,
% 3.45/0.99      ( m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
% 3.45/0.99      | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_2463,c_51,c_53,c_939,c_3187]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3388,plain,
% 3.45/0.99      ( k1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != sK3
% 3.45/0.99      | m1_subset_1(k2_partfun1(sK2,sK5,sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_relat_1(k2_partfun1(sK2,sK5,sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_3387]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6084,plain,
% 3.45/0.99      ( k1_relat_1(k7_relat_1(sK6,sK3)) != sK3
% 3.45/0.99      | m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_6080,c_3388]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_45,negated_conjecture,
% 3.45/0.99      ( r1_tarski(sK3,sK2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2484,plain,
% 3.45/0.99      ( r1_tarski(sK3,sK2) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_36,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.45/0.99      | k1_xboole_0 = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_47,negated_conjecture,
% 3.45/0.99      ( v1_funct_2(sK6,sK2,sK5) ),
% 3.45/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_768,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.45/0.99      | sK6 != X0
% 3.45/0.99      | sK5 != X2
% 3.45/0.99      | sK2 != X1
% 3.45/0.99      | k1_xboole_0 = X2 ),
% 3.45/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_47]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_769,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK5)))
% 3.45/0.99      | k1_relset_1(sK2,sK5,sK6) = sK2
% 3.45/0.99      | k1_xboole_0 = sK5 ),
% 3.45/0.99      inference(unflattening,[status(thm)],[c_768]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_771,plain,
% 3.45/0.99      ( k1_relset_1(sK2,sK5,sK6) = sK2 | k1_xboole_0 = sK5 ),
% 3.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_769,c_46]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_25,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2492,plain,
% 3.45/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4110,plain,
% 3.45/0.99      ( k1_relset_1(sK2,sK5,sK6) = k1_relat_1(sK6) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2483,c_2492]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4249,plain,
% 3.45/0.99      ( k1_relat_1(sK6) = sK2 | sK5 = k1_xboole_0 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_771,c_4110]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_49,negated_conjecture,
% 3.45/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.45/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7,plain,
% 3.45/0.99      ( v1_xboole_0(sK1(X0)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ v1_xboole_0(X1)
% 3.45/0.99      | v1_xboole_0(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_442,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.45/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_366]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2906,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,sK1(X1)) | v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X1)) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3626,plain,
% 3.45/0.99      ( ~ r1_tarski(k1_xboole_0,sK1(X0))
% 3.45/0.99      | ~ v1_xboole_0(sK1(X0))
% 3.45/0.99      | v1_xboole_0(k1_xboole_0) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_2906]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3627,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,sK1(X0)) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1447,plain,
% 3.45/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.45/0.99      theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4053,plain,
% 3.45/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1447]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4055,plain,
% 3.45/0.99      ( v1_xboole_0(sK5) | ~ v1_xboole_0(k1_xboole_0) | sK5 != k1_xboole_0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_4053]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4324,plain,
% 3.45/0.99      ( k1_relat_1(sK6) = sK2 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4249,c_49,c_7,c_3626,c_3627,c_4055]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_20,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2495,plain,
% 3.45/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.45/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4729,plain,
% 3.45/0.99      ( k1_relat_1(k7_relat_1(sK6,X0)) = X0
% 3.45/0.99      | r1_tarski(X0,sK2) != iProver_top
% 3.45/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4324,c_2495]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3447,plain,
% 3.45/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK2,sK5)) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2483,c_2499]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3948,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK5)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3447,c_2478]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4089,plain,
% 3.45/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.45/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3948,c_2498]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5141,plain,
% 3.45/0.99      ( r1_tarski(X0,sK2) != iProver_top
% 3.45/0.99      | k1_relat_1(k7_relat_1(sK6,X0)) = X0 ),
% 3.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4729,c_4089]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5142,plain,
% 3.45/0.99      ( k1_relat_1(k7_relat_1(sK6,X0)) = X0
% 3.45/0.99      | r1_tarski(X0,sK2) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_5141]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5152,plain,
% 3.45/0.99      ( k1_relat_1(k7_relat_1(sK6,sK3)) = sK3 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2484,c_5142]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6131,plain,
% 3.45/0.99      ( sK3 != sK3
% 3.45/0.99      | m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(light_normalisation,[status(thm)],[c_6084,c_5152]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6132,plain,
% 3.45/0.99      ( m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(equality_resolution_simp,[status(thm)],[c_6131]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9039,plain,
% 3.45/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK6,sK3)),sK3) != iProver_top
% 3.45/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK6,sK3)),sK4) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2490,c_6132]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9043,plain,
% 3.45/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK6,sK3)),sK4) != iProver_top
% 3.45/0.99      | r1_tarski(sK3,sK3) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(light_normalisation,[status(thm)],[c_9039,c_5152]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_17,plain,
% 3.45/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2497,plain,
% 3.45/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4091,plain,
% 3.45/0.99      ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4089,c_2497]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9044,plain,
% 3.45/0.99      ( r1_tarski(k9_relat_1(sK6,sK3),sK4) != iProver_top
% 3.45/0.99      | r1_tarski(sK3,sK3) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_9043,c_4091]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_26,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2491,plain,
% 3.45/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4213,plain,
% 3.45/0.99      ( k7_relset_1(sK2,sK5,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2483,c_2491]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_44,negated_conjecture,
% 3.45/0.99      ( r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) ),
% 3.45/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2485,plain,
% 3.45/0.99      ( r1_tarski(k7_relset_1(sK2,sK5,sK6,sK3),sK4) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4253,plain,
% 3.45/0.99      ( r1_tarski(k9_relat_1(sK6,sK3),sK4) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_4213,c_2485]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_11877,plain,
% 3.45/0.99      ( r1_tarski(sK3,sK3) != iProver_top
% 3.45/0.99      | v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9044,c_4253]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f123]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2504,plain,
% 3.45/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_11883,plain,
% 3.45/0.99      ( v1_relat_1(k7_relat_1(sK6,sK3)) != iProver_top ),
% 3.45/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11877,c_2504]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12788,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_12779,c_11883]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ General
% 3.45/0.99  
% 3.45/0.99  abstr_ref_over_cycles:                  0
% 3.45/0.99  abstr_ref_under_cycles:                 0
% 3.45/0.99  gc_basic_clause_elim:                   0
% 3.45/0.99  forced_gc_time:                         0
% 3.45/0.99  parsing_time:                           0.013
% 3.45/0.99  unif_index_cands_time:                  0.
% 3.45/0.99  unif_index_add_time:                    0.
% 3.45/0.99  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.012
% 3.45/1.00  total_time:                             0.322
% 3.45/1.00  num_of_symbols:                         57
% 3.45/1.00  num_of_terms:                           12661
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          0
% 3.45/1.00  num_of_split_atoms:                     0
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    30
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        0
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       221
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        55
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        6
% 3.45/1.00  pred_elim:                              3
% 3.45/1.00  pred_elim_cl:                           -2
% 3.45/1.00  pred_elim_cycles:                       5
% 3.45/1.00  merged_defs:                            8
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          11
% 3.45/1.00  prep_cycles:                            4
% 3.45/1.00  pred_elim_time:                         0.012
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.001
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                48
% 3.45/1.00  conjectures:                            5
% 3.45/1.00  epr:                                    11
% 3.45/1.00  horn:                                   40
% 3.45/1.00  ground:                                 14
% 3.45/1.00  unary:                                  10
% 3.45/1.00  binary:                                 10
% 3.45/1.00  lits:                                   142
% 3.45/1.00  lits_eq:                                34
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                3
% 3.45/1.00  fd_pseudo_cond:                         1
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      29
% 3.45/1.00  prop_fast_solver_calls:                 1738
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    5214
% 3.45/1.00  prop_preprocess_simplified:             13213
% 3.45/1.00  prop_fo_subsumed:                       35
% 3.45/1.00  prop_solver_time:                       0.
% 3.45/1.00  smt_solver_time:                        0.
% 3.45/1.00  smt_fast_solver_time:                   0.
% 3.45/1.00  prop_fast_solver_time:                  0.
% 3.45/1.00  prop_unsat_core_time:                   0.
% 3.45/1.00  
% 3.45/1.00  ------ QBF
% 3.45/1.00  
% 3.45/1.00  qbf_q_res:                              0
% 3.45/1.00  qbf_num_tautologies:                    0
% 3.45/1.00  qbf_prep_cycles:                        0
% 3.45/1.00  
% 3.45/1.00  ------ BMC1
% 3.45/1.00  
% 3.45/1.00  bmc1_current_bound:                     -1
% 3.45/1.00  bmc1_last_solved_bound:                 -1
% 3.45/1.00  bmc1_unsat_core_size:                   -1
% 3.45/1.00  bmc1_unsat_core_parents_size:           -1
% 3.45/1.00  bmc1_merge_next_fun:                    0
% 3.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation
% 3.45/1.00  
% 3.45/1.00  inst_num_of_clauses:                    1343
% 3.45/1.00  inst_num_in_passive:                    602
% 3.45/1.00  inst_num_in_active:                     492
% 3.45/1.00  inst_num_in_unprocessed:                251
% 3.45/1.00  inst_num_of_loops:                      660
% 3.45/1.00  inst_num_of_learning_restarts:          0
% 3.45/1.00  inst_num_moves_active_passive:          165
% 3.45/1.00  inst_lit_activity:                      0
% 3.45/1.00  inst_lit_activity_moves:                0
% 3.45/1.00  inst_num_tautologies:                   0
% 3.45/1.00  inst_num_prop_implied:                  0
% 3.45/1.00  inst_num_existing_simplified:           0
% 3.45/1.00  inst_num_eq_res_simplified:             0
% 3.45/1.00  inst_num_child_elim:                    0
% 3.45/1.00  inst_num_of_dismatching_blockings:      511
% 3.45/1.00  inst_num_of_non_proper_insts:           1121
% 3.45/1.00  inst_num_of_duplicates:                 0
% 3.45/1.00  inst_inst_num_from_inst_to_res:         0
% 3.45/1.00  inst_dismatching_checking_time:         0.
% 3.45/1.00  
% 3.45/1.00  ------ Resolution
% 3.45/1.00  
% 3.45/1.00  res_num_of_clauses:                     0
% 3.45/1.00  res_num_in_passive:                     0
% 3.45/1.00  res_num_in_active:                      0
% 3.45/1.00  res_num_of_loops:                       225
% 3.45/1.00  res_forward_subset_subsumed:            34
% 3.45/1.00  res_backward_subset_subsumed:           4
% 3.45/1.00  res_forward_subsumed:                   0
% 3.45/1.00  res_backward_subsumed:                  0
% 3.45/1.00  res_forward_subsumption_resolution:     3
% 3.45/1.00  res_backward_subsumption_resolution:    0
% 3.45/1.00  res_clause_to_clause_subsumption:       579
% 3.45/1.00  res_orphan_elimination:                 0
% 3.45/1.00  res_tautology_del:                      67
% 3.45/1.00  res_num_eq_res_simplified:              0
% 3.45/1.00  res_num_sel_changes:                    0
% 3.45/1.00  res_moves_from_active_to_pass:          0
% 3.45/1.00  
% 3.45/1.00  ------ Superposition
% 3.45/1.00  
% 3.45/1.00  sup_time_total:                         0.
% 3.45/1.00  sup_time_generating:                    0.
% 3.45/1.00  sup_time_sim_full:                      0.
% 3.45/1.00  sup_time_sim_immed:                     0.
% 3.45/1.00  
% 3.45/1.00  sup_num_of_clauses:                     216
% 3.45/1.00  sup_num_in_active:                      118
% 3.45/1.00  sup_num_in_passive:                     98
% 3.45/1.00  sup_num_of_loops:                       131
% 3.45/1.00  sup_fw_superposition:                   112
% 3.45/1.00  sup_bw_superposition:                   117
% 3.45/1.00  sup_immediate_simplified:               41
% 3.45/1.00  sup_given_eliminated:                   0
% 3.45/1.00  comparisons_done:                       0
% 3.45/1.00  comparisons_avoided:                    1
% 3.45/1.00  
% 3.45/1.00  ------ Simplifications
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  sim_fw_subset_subsumed:                 7
% 3.45/1.00  sim_bw_subset_subsumed:                 1
% 3.45/1.00  sim_fw_subsumed:                        13
% 3.45/1.00  sim_bw_subsumed:                        1
% 3.45/1.00  sim_fw_subsumption_res:                 7
% 3.45/1.00  sim_bw_subsumption_res:                 0
% 3.45/1.00  sim_tautology_del:                      5
% 3.45/1.00  sim_eq_tautology_del:                   7
% 3.45/1.00  sim_eq_res_simp:                        1
% 3.45/1.00  sim_fw_demodulated:                     8
% 3.45/1.00  sim_bw_demodulated:                     13
% 3.45/1.00  sim_light_normalised:                   15
% 3.45/1.00  sim_joinable_taut:                      0
% 3.45/1.00  sim_joinable_simp:                      0
% 3.45/1.00  sim_ac_normalised:                      0
% 3.45/1.00  sim_smt_subsumption:                    0
% 3.45/1.00  
%------------------------------------------------------------------------------
